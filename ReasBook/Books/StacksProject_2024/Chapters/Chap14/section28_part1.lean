import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_28_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

/-- The constant `0`-simplex of `Δ[1]` in cosimplicial degree `n`. -/
def deltaOneZeroEndpoint
    (n : SimplexCategory) : (Δ[1] : SSet).obj (op n) :=
  SSet.stdSimplex.const 1 0 (op n)

/-- The constant `1`-simplex of `Δ[1]` in cosimplicial degree `n`. -/
def deltaOneOneEndpoint
    (n : SimplexCategory) : (Δ[1] : SSet).obj (op n) :=
  SSet.stdSimplex.const 1 1 (op n)

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {U V : CosimplicialObject C}

/- Domain-style sampling for Definition 14.28.1:
- primary domain: cosimplicial homotopies defined through the standard `1`-simplex cotensor;
- inspected same-kind owner declarations:
  `CategoryTheory.homFromSimplicialSet`,
  `CategoryTheory.homFromSimplicialSet_map_π`,
  `CategoryTheory.SimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopic`,
  `Relation.EqvGen`;
- target layer: `source-facing`;
- core/canonical owner:
  `homFromSimplicialSet (Δ[1] : SSet) V`, built from the more general owner
  `homFromCosimplicialSet`;
- canonical owner for the zigzag relation: `Relation.EqvGen` on directed homotopies;
- bridge/view data: degreewise evaluation at a simplex `α : [n] ⟶ [1]`, derived from the
  source-facing owner and its canonical projection square `homFromSimplicialSet_map_π`.
-/

/-- Definition 14.28.1: a homotopy from `a` to `b` is a morphism `U ⟶ Hom(Δ[1], V)` whose
endpoint evaluations recover `a` and `b`. -/
structure Homotopy (a b : U ⟶ V) where
  /-- The underlying map to the standard `1`-simplex cotensor. -/
  hom : U ⟶ homFromSimplicialSet (Δ[1] : SSet) V
  /-- Evaluation at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (deltaOneZeroEndpoint n) =
      a.app n
  /-- Evaluation at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (deltaOneOneEndpoint n) =
      b.app n

namespace Homotopy

@[ext] theorem ext {a b : U ⟶ V} {H K : Homotopy a b}
    (h : H.hom = K.hom) : H = K := by
  cases H with
  | mk hom zero_endpoint one_endpoint =>
    cases K with
    | mk hom' zero_endpoint' one_endpoint' =>
      cases h
      have hzero : zero_endpoint = zero_endpoint' := Subsingleton.elim _ _
      cases hzero
      have hone : one_endpoint = one_endpoint' := Subsingleton.elim _ _
      cases hone
      rfl

/-- Evaluating a cosimplicial homotopy at a simplex of `Δ[1]` gives the corresponding degreewise
component map `U_n ⟶ V_n`. -/
def app {a b : U ⟶ V} (H : Homotopy a b) {n : SimplexCategory}
    (α : (Δ[1] : SSet).obj (op n)) : U.obj n ⟶ V.obj n :=
  H.hom.app n ≫ Pi.π (fun _ ↦ V.obj n) α

instance {a b : U ⟶ V} :
    CoeFun (Homotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
      (Δ[1] : SSet).obj (op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} α ↦ H.app α

@[simp] theorem app_zero_endpoint {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (deltaOneZeroEndpoint n) = a.app n :=
  H.zero_endpoint n

@[simp] theorem app_one_endpoint {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (deltaOneOneEndpoint n) = b.app n :=
  H.one_endpoint n

/-- Evaluating a cosimplicial homotopy at a simplex of `Δ[1]` is compatible with the
cosimplicial structure maps via the canonical commutative square. -/
theorem naturality {a b : U ⟶ V} (H : Homotopy a b)
    {m n : SimplexCategory} (f : n ⟶ m) (α : (Δ[1] : SSet).obj (op m)) :
    CommSq (U.map f) (H ((Δ[1] : SSet).map f.op α)) (H α) (V.map f) := by
  simpa [Homotopy.app] using
    (homFromSimplicialSet_hom_naturality
      (U := (Δ[1] : SSet))
      (V := V)
      H.hom
      f
      α)

end Homotopy

/-- Two morphisms of cosimplicial objects are homotopic if they are connected by a finite zigzag
of directed cosimplicial homotopies. -/
def Homotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen
    (fun f g : U ⟶ V ↦ Nonempty (Homotopy f g))
    a b

@[refl] lemma Homotopic.refl (a : U ⟶ V) : Homotopic a a :=
  Relation.EqvGen.refl a

@[symm] lemma Homotopic.symm {a b : U ⟶ V} (h : Homotopic a b) : Homotopic b a := by
  simpa [Homotopic] using Relation.EqvGen.symm a b h

@[trans] lemma Homotopic.trans {a b c : U ⟶ V}
    (hab : Homotopic a b) (hbc : Homotopic b c) : Homotopic a c := by
  simpa [Homotopic] using Relation.EqvGen.trans a b c hab hbc

-- Proof sketch: a directed cosimplicial homotopy is one generating relation for the equivalence
-- closure defining `Homotopic`.
/-- A directed cosimplicial homotopy gives the associated zigzag homotopy relation. -/
lemma Homotopic.of_homotopy {a b : U ⟶ V} (h : Homotopy a b) : Homotopic a b :=
  Relation.EqvGen.rel a b ⟨h⟩

end CategoryTheory.CosimplicialObject

/-! ### Remark_14_28_2 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

universe u v u' v'

noncomputable section

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

/- Domain-style sampling for Remark 14.28.2:
- primary domain: cosimplicial homotopies for cosimplicial objects, with the product-free
  `Δ[1]`-indexed family description bridged to the canonical cotensor-style owner;
- inspected same-kind owner declarations:
  `CategoryTheory.homFromCosimplicialSet`,
  `CategoryTheory.homFromCosimplicialSet_map_π`,
  `CategoryTheory.CosimplicialObject.Homotopy`,
  `CategoryTheory.CosimplicialObject.Homotopic`;
- best owner abstraction: the canonical owner remains `Homotopy a b`, built from
  `homFromCosimplicialSet (Δ[1] : SSet) V`;
- primitive data here are exactly the degreewise maps `h_{n,α}` with endpoints and naturality;
  the `Hom(Δ[1], V)`-valued map and the zigzag relation are derived by bridge constructions, so
  this file should keep the source-facing family formulation but reuse the upstream owner API for
  the canonical comparison. -/

/-- Remark 14.28.2: a product-free homotopy from `a` to `b` is a family of maps
`h_{n,\alpha} : U_n ⟶ V_n`, indexed by simplices `α ∈ Δ[1]_n`, with the specified endpoints and
naturality. In categories with finite products this is equivalent to the `Hom(Δ[1], V)`-based
formulation of Definition 14.28.1. -/
structure DeltaOneHomotopy (a b : U ⟶ V) where
  /-- The degreewise component indexed by a simplex `α : [n] ⟶ [1]`. -/
  hom {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (Opposite.op n)) : U.obj n ⟶ V.obj n
  /-- The component at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom (deltaOneZeroEndpoint n) = a.app n
  /-- The component at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom (deltaOneOneEndpoint n) = b.app n
  /-- The family `h_{n,\alpha}` is natural in the simplex operator via the canonical
  commutative square. -/
  naturality {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
      (i : (Δ[1] : SSet).obj (Opposite.op n₂)) :
    CommSq (U.map σ) (hom ((Δ[1] : SSet).map σ.op i)) (hom i) (V.map σ)

namespace DeltaOneHomotopy

@[ext] theorem ext {H K : DeltaOneHomotopy a b}
    (h : ∀ ⦃n : SimplexCategory⦄, (i : (Δ[1] : SSet.{0}).obj (Opposite.op n)) →
      H.hom i = K.hom i) : H = K := by
  cases H with
  | mk hom zero_endpoint one_endpoint naturality =>
    cases K with
    | mk hom' zero_endpoint' one_endpoint' naturality' =>
      have hhom : @hom = @hom' := by
        funext n i
        exact h i
      cases hhom
      have hzero : zero_endpoint = zero_endpoint' := Subsingleton.elim _ _
      cases hzero
      have hone : one_endpoint = one_endpoint' := Subsingleton.elim _ _
      cases hone
      have hnat : @naturality = @naturality' := by
        exact Subsingleton.elim _ _
      cases hnat
      rfl

/-- A `Δ[1]`-indexed homotopy can be evaluated at a simplex in each degree to recover its
underlying family of component morphisms. -/
instance :
    CoeFun (DeltaOneHomotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
      (Δ[1] : SSet.{0}).obj (Opposite.op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} i ↦ H.hom i

/-- Any functor carries a `Δ[1]`-indexed homotopy to the induced `Δ[1]`-indexed homotopy between
the whiskered morphisms. -/
def whiskerRight (H : DeltaOneHomotopy a b) (F : C ⥤ D) :
    DeltaOneHomotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) where
  hom i := F.map (H.hom i)
  zero_endpoint n := by
    simpa using congrArg F.map (H.zero_endpoint n)
  one_endpoint n := by
    simpa using congrArg F.map (H.one_endpoint n)
  naturality σ i := by
    simpa using (H.naturality σ i).map F

section

variable [HasFiniteProducts C]

/-- In a category with finite products, a `Δ[1]`-indexed family of components assembles into the
canonical `Hom(Δ[1], V)`-valued cosimplicial homotopy. -/
def toHomotopy (H : DeltaOneHomotopy a b) : Homotopy a b where
  hom :=
    { app := fun n ↦ Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
      naturality := by
        intro n₁ n₂ σ
        apply Pi.hom_ext
        intro i
        calc
          (U.map σ ≫
              Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₂) ↦ H.hom i)) ≫
              Pi.π (fun _ ↦ V.obj n₂) i
              = U.map σ ≫ H.hom i := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ U.map σ ≫ k)
                      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₂) ↦ H.hom i) i)
          _ = H.hom ((Δ[1] : SSet).map σ.op i) ≫ V.map σ := (H.naturality σ i).w
          _ = ((Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫
                Pi.π (fun _ ↦ V.obj n₁) ((Δ[1] : SSet).map σ.op i)) ≫ V.map σ := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ V.map σ)
                      (Pi.lift_π
                        (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)
                        ((Δ[1] : SSet).map σ.op i)).symm
          _ = ((Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫
                (homFromSimplicialSet (Δ[1] : SSet) V).map σ) ≫
                Pi.π (fun _ ↦ V.obj n₂) i := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦
                        (Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n₁) ↦ H.hom i)) ≫ k)
                      ((homFromSimplicialSet_map_π (Δ[1] : SSet) V σ i).w).symm }
  zero_endpoint n := by
    exact
      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
        (deltaOneZeroEndpoint n)).trans (H.zero_endpoint n)
  one_endpoint n := by
    exact
      (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i)
        (deltaOneOneEndpoint n)).trans (H.one_endpoint n)

/-- The canonical `Hom(Δ[1], V)`-valued homotopy can be evaluated at each simplex of `Δ[1]` to
recover the product-free family formulation. -/
def ofHomotopy (H : Homotopy a b) : DeltaOneHomotopy a b where
  hom i := H.app i
  zero_endpoint := H.app_zero_endpoint
  one_endpoint := H.app_one_endpoint
  naturality σ i := by
    simpa [Homotopy.app] using H.naturality σ i

@[simp] theorem ofHomotopy_toHomotopy (H : DeltaOneHomotopy a b) :
    ofHomotopy H.toHomotopy = H := by
  apply ext
  intro n i
  simpa [ofHomotopy, toHomotopy] using
    Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.hom i) i

@[simp] theorem toHomotopy_ofHomotopy (H : Homotopy a b) :
    (ofHomotopy H).toHomotopy = H := by
  apply Homotopy.ext
  ext n
  apply Pi.hom_ext
  intro i
  simpa [ofHomotopy, toHomotopy] using
    (Pi.lift_π (fun i : (Δ[1] : SSet.{0}).obj (Opposite.op n) ↦ H.app i) i)

/-- Under finite products, the source-facing `Δ[1]`-indexed family formulation and the canonical
cotensor-valued homotopy notion are equivalent as directed homotopy data. -/
def equivHomotopy : DeltaOneHomotopy a b ≃ Homotopy a b where
  toFun := toHomotopy
  invFun := ofHomotopy
  left_inv := ofHomotopy_toHomotopy
  right_inv := toHomotopy_ofHomotopy

end

end DeltaOneHomotopy

/-- Two morphisms of cosimplicial objects are `Δ[1]`-homotopic if they are connected by a finite
zigzag of directed `Δ[1]`-indexed homotopies in either direction. -/
def DeltaOneHomotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen (fun f g : U ⟶ V ↦ Nonempty (DeltaOneHomotopy f g)) a b

@[refl] lemma DeltaOneHomotopic.refl (a : U ⟶ V) : DeltaOneHomotopic a a :=
  Relation.EqvGen.refl a

@[symm] lemma DeltaOneHomotopic.symm {a b : U ⟶ V} (h : DeltaOneHomotopic a b) :
    DeltaOneHomotopic b a := by
  simpa [DeltaOneHomotopic] using Relation.EqvGen.symm a b h

@[trans] lemma DeltaOneHomotopic.trans {a b c : U ⟶ V}
    (hab : DeltaOneHomotopic a b) (hbc : DeltaOneHomotopic b c) :
    DeltaOneHomotopic a c := by
  simpa [DeltaOneHomotopic] using Relation.EqvGen.trans a b c hab hbc

-- Proof sketch: a directed `Δ[1]`-indexed homotopy contributes one generating step in the
-- defining relation for `DeltaOneHomotopic`, so apply `Relation.EqvGen.rel`.
/-- A directed `Δ[1]`-indexed homotopy gives the corresponding zigzag homotopy relation. -/
theorem DeltaOneHomotopic.of_homotopy (h : DeltaOneHomotopy a b) :
    DeltaOneHomotopic a b :=
  Relation.EqvGen.rel a b ⟨h⟩

-- Proof sketch: send each generating directed homotopy step of the zigzag to its image under
-- `DeltaOneHomotopy.whiskerRight`; the induced map on generators extends to the whiskered
-- zigzag.
/-- Functors preserve the zigzag relation generated by `Δ[1]`-indexed cosimplicial homotopies. -/
theorem DeltaOneHomotopic.whiskerRight (h : DeltaOneHomotopic a b) (F : C ⥤ D) :
    DeltaOneHomotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F) := by
  induction h with
  | rel x y hxy =>
      exact DeltaOneHomotopic.of_homotopy (hxy.some.whiskerRight F)
  | refl x =>
      exact DeltaOneHomotopic.refl (Functor.whiskerRight x F)
  | symm x y hxy ih =>
      exact DeltaOneHomotopic.symm ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact DeltaOneHomotopic.trans ihxy ihyz

section

variable [HasFiniteProducts C]

/-- Under finite products, the zigzag relation generated by the product-free `Δ[1]`-indexed
families agrees with the canonical cotensor-valued homotopy relation. -/
theorem deltaOneHomotopic_iff_homotopic :
    DeltaOneHomotopic a b ↔ Homotopic a b := by
  refine ⟨?_, ?_⟩
  · intro h
    simpa [DeltaOneHomotopic, Homotopic] using
      (Relation.EqvGen.mono
        (fun x y hxy ↦ ⟨hxy.some.toHomotopy⟩)
        h)
  · intro h
    simpa [DeltaOneHomotopic, Homotopic] using
      (Relation.EqvGen.mono
        (fun x y hxy ↦ ⟨DeltaOneHomotopy.ofHomotopy hxy.some⟩)
        h)

end

end CategoryTheory.CosimplicialObject

/-! ### Lemma_14_28_3 (from Chap14) -/
open CategoryTheory
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.28.3:
- primary domain: simplicial and cosimplicial homotopy data under the standard opposite
  anti-equivalence;
- inspected same-kind owner declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopy`,
  `CategoryTheory.CosimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopy`,
  `NatTrans.op`,
  `SSet.stdSimplex.objMk₁`;
- best owner abstraction: the target-side canonical owner is
  `CategoryTheory.SimplicialObject.Homotopy`, while the source-facing owner remains
  `DeltaOneHomotopy`, and the bridge/view is the canonical opposite natural transformation
  `NatTrans.op a`;
- primitive data: the degreewise `Δ[1]`-indexed family in `DeltaOneHomotopy` and the
  combinatorial operators `h n i` in `SimplicialObject.Homotopy`;
- derived API: the existence statements and the induced zigzag relations.

Source/core/bridge triage:
- `source-facing`: the equivalence between `DeltaOneHomotopy a b` and simplicial homotopy on the
  opposite simplicial maps;
- `core/canonical`: `SimplicialObject.Homotopy`;
- `bridge/view`: `NatTrans.op` on cosimplicial morphisms. -/

namespace DeltaOneHomotopy

private noncomputable def simplexIndexEquiv (n : ℕ) :
    Fin (n + 2) ≃ (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) :=
  Equiv.ofBijective SSet.stdSimplex.objMk₁ SSet.stdSimplex.objMk₁_bijective

/-- Helper for Lemma 14.28.3: the constant `0` simplex of `Δ[1]` is the last simplex in the
canonical `Fin` indexing of `Δ[1]_n`. -/
private lemma deltaOneZeroEndpoint_eq_objMk₁_last (n : ℕ) :
    deltaOneZeroEndpoint ⦋n⦌ = SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
  -- Both simplices are the constant map with value `0`, so compare them on every vertex.
  ext j : 1
  rw [SSet.stdSimplex.objMk₁_of_castSucc_lt _ _ j.castSucc_lt_last]
  simp [deltaOneZeroEndpoint, SSet.stdSimplex.const]

/-- Helper for Lemma 14.28.3: the constant `1` simplex of `Δ[1]` is the zero simplex in the
canonical `Fin` indexing of `Δ[1]_n`. -/
private lemma deltaOneOneEndpoint_eq_objMk₁_zero (n : ℕ) :
    deltaOneOneEndpoint ⦋n⦌ = SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) := by
  -- Both simplices are the constant map with value `1`, so compare them on every vertex.
  ext j : 1
  rw [SSet.stdSimplex.objMk₁_of_le_castSucc _ _ (by simp)]
  simp [deltaOneOneEndpoint, SSet.stdSimplex.const]

/-- Helper for Lemma 14.28.3: rewriting the action of a face map on the canonical `objMk₁`
simplex into the `Δ[1].δ` notation exposes the standard `stdSimplex` normalization lemmas. -/
private lemma delta_one_map_objMk₁_delta {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j).op (SSet.stdSimplex.objMk₁ i)) =
      Δ[1].δ j (SSet.stdSimplex.objMk₁ i) := by
  rfl

/-- Helper for Lemma 14.28.3: rewriting the action of a degeneracy map on the canonical `objMk₁`
simplex into the `Δ[1].σ` notation exposes the standard `stdSimplex` normalization lemmas. -/
private lemma delta_one_map_objMk₁_sigma {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ j).op (SSet.stdSimplex.objMk₁ i)) =
      Δ[1].σ j (SSet.stdSimplex.objMk₁ i) := by
  rfl

/-- Helper for Lemma 14.28.3: the interior face of the higher canonical simplex lands on the
canonical middle simplex used by the forward homotopy formula. -/
private lemma delta_one_face_objMk₁_succ_succ_castSucc {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.castSucc).op
      (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the `δ_objMk₁_of_lt` branch, followed by the canonical predecessor normalization.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt]
  · simp
  · have hij' : (i : ℕ) ≤ (j : ℕ) := by
      simpa using hij
    show (i.castSucc.castSucc : Fin (n + 4)).1 <
        (j.succ.succ.castSucc : Fin (n + 4)).1
    simp
    omega

/-- Helper for Lemma 14.28.3: the left adjacent face in the middle branch again yields the
canonical middle simplex. -/
private lemma delta_one_face_objMk₁_adjacent_left {n : ℕ} (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
      (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the special `δ_objMk₁_of_lt` branch at the adjacent face.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by simp)]
  simp

/-- Helper for Lemma 14.28.3: the right adjacent face in the middle branch yields the same
canonical middle simplex. -/
private lemma delta_one_face_objMk₁_adjacent_right {n : ℕ} (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
      (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the complementary `δ_objMk₁_of_le` branch at the adjacent face.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
  have hIndex :
      j.castSucc.castSucc.succ.castPred (by simp) = j.succ.castSucc := by
    ext
    simp
  simp [hIndex]

/-- Helper for Lemma 14.28.3: the interior degeneracy branch for `i ≤ j` lands on the next
canonical middle simplex. -/
private lemma delta_one_sigma_objMk₁_of_le {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.castSucc).op
      (SSet.stdSimplex.objMk₁ j.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.succ.castSucc := by
  -- This is the `σ_objMk₁_of_lt` branch after translating `i ≤ j` to the casted inequality.
  rw [delta_one_map_objMk₁_sigma]
  rw [SSet.stdSimplex.σ_objMk₁_of_lt _ _]
  · rfl
  · simpa using hij

/-- Helper for Lemma 14.28.3: the complementary interior degeneracy branch for `j ≤ i` lands on
the cast-successor canonical simplex used by the second simplicial-degeneracy axiom. -/
private lemma delta_one_sigma_objMk₁_of_gt {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.succ).op
      (SSet.stdSimplex.objMk₁ j.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc := by
  -- This is the `σ_objMk₁_of_le` branch after translating the complementary inequality.
  rw [delta_one_map_objMk₁_sigma]
  rw [SSet.stdSimplex.σ_objMk₁_of_le _ _]
  · simp
  · simpa using hji

-- Proof sketch: the simplicial homotopy operators are the opposite of the nondegenerate
-- `Δ[1]`-components in degree `n + 1`, followed by the target degeneracy map. The simplicial
-- identities follow from the naturality squares of `H` together with the relations for
-- `SSet.stdSimplex.objMk₁`.
private def toOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  h i := (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫ V.map (SimplexCategory.σ i)).op
  h_zero_comp_δ_zero n := by
    -- Route correction: the forward proof works by proving the corresponding equality in `C`,
    -- using the `Δ[1]` face normalization, and then taking opposites.
    have hnat :
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) =
          H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ V.δ 0 := by
      simpa [CosimplicialObject.δ, delta_one_map_objMk₁_delta] using
        (H.naturality (SimplexCategory.δ (0 : Fin (n + 2)))
          (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc)).w
    have hEq :
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) ≫ V.σ 0 =
          b.app ⦋n⦌ := by
      calc
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) ≫ V.σ 0 =
            (U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc)) ≫ V.σ 0 := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ V.δ 0) ≫ V.σ 0 := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ (V.δ 0 ≫ V.σ 0) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) := by
              simpa using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ k)
                  (V.δ_comp_σ_self (i := (0 : Fin (n + 1))))
        _ = b.app ⦋n⦌ := by
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using H.one_endpoint ⦋n⦌
    -- Unop the simplicial-object target equality back to the cosimplicial statement above.
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_last_comp_δ_last n := by
    -- Normalize the last face to the constant-`0` simplex and then use the `δσ = id` relation.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ (Fin.last (n + 1))).op
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)) =
            SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
      rw [delta_one_map_objMk₁_delta]
      simpa using
        (SSet.stdSimplex.δ_objMk₁_of_le
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 1))
          (by simp))
    have hnat :
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) =
          H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫ V.δ (Fin.last (n + 1)) := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ (Fin.last (n + 1)))
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)).w
    have hEq :
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) ≫
              V.σ (Fin.last n) =
          a.app ⦋n⦌ := by
      calc
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) ≫
              V.σ (Fin.last n) =
          (U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)) ≫
              V.σ (Fin.last n) := by
                simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫
              V.δ (Fin.last (n + 1))) ≫
                V.σ (Fin.last n) := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫
              (V.δ (Fin.last (n + 1)) ≫ V.σ (Fin.last n)) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) := by
              rw [show V.δ (Fin.last (n + 1)) ≫ V.σ (Fin.last n) = 𝟙 _ by
                simpa using (V.δ_comp_σ_succ (i := Fin.last n))]
              rw [Category.comp_id]
        _ = a.app ⦋n⦌ := by
              simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using H.zero_endpoint ⦋n⦌
    -- Unop the endpoint equality back to the simplicial-object goal.
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    -- Normalize the interior face to the canonical middle simplex, then use the second
    -- cosimplicial identity to move the target `δ` past the target `σ`.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_succ_succ_castSucc i j hij
    have hnat :
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.castSucc := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ i.castSucc)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)).w
    have hEq :
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
      calc
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
            (U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) ≫
              V.σ j.succ := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.castSucc) ≫ V.σ j.succ := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ i.castSucc ≫ V.σ j.succ) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ (V.σ j ≫ V.δ i) := by
              rw [V.δ_comp_σ_of_le hij]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_succ_comp_δ_castSucc_succ j := by
    -- Normalize both adjacent faces to the same middle simplex, then apply the two special
    -- `δσ = id` identities on the target.
    have hmap_left :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_adjacent_left j
    have hmap_right :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_adjacent_right j
    have hnat_left :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ := by
      simpa [CosimplicialObject.δ, hmap_left] using
        (H.naturality (SimplexCategory.δ j.castSucc.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)).w
    have hnat_right :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ := by
      simpa [CosimplicialObject.δ, hmap_right] using
        (H.naturality (SimplexCategory.δ j.castSucc.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)).w
    have hEq :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
          U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫
            V.σ j.castSucc := by
      calc
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
            (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ) ≫
              V.σ j.succ := by
              simpa [Category.assoc] using hnat_left =≫ V.σ j.succ
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ j.castSucc.succ ≫ V.σ j.succ) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ k)
                  (V.δ_comp_σ_self (i := j.succ))
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ j.castSucc.succ ≫ V.σ j.castSucc) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ k)
                  (V.δ_comp_σ_succ (i := j.castSucc)).symm
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ) ≫
              V.σ j.castSucc := by
              simp [Category.assoc]
        _ = U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫
              V.σ j.castSucc := by
              simpa [Category.assoc] using (hnat_right =≫ V.σ j.castSucc).symm
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    -- Normalize the complementary interior face to the same middle simplex, then use the
    -- fourth cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      rw [delta_one_map_objMk₁_delta]
      rw [SSet.stdSimplex.δ_objMk₁_of_le]
      · have hlt : j.castSucc.castSucc.succ < Fin.last _ := by
          show (j.castSucc.castSucc.succ : Fin _).1 < (Fin.last _ : Fin _).1
          have hj : (j : ℕ) < _ := j.is_lt
          simp
          omega
        have hIndex :
            j.castSucc.castSucc.succ.castPred
                (Fin.ne_last_of_lt hlt) =
              j.castSucc.succ := by
          ext
          simp
        simp [hIndex]
      · show (j.castSucc.castSucc.succ : Fin _).1 ≤ (i.succ.castSucc : Fin _).1
        have hji' : (j : ℕ) < (i : ℕ) := by
          simpa using hji
        simp
        omega
    have hnat :
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.succ := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ i.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)).w
    have hEq :
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫ V.σ j.castSucc =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
      calc
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫ V.σ j.castSucc =
            (U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) ≫
              V.σ j.castSucc := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.succ) ≫
              V.σ j.castSucc := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ i.succ ≫ V.σ j.castSucc) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ (V.σ j ≫ V.δ i) := by
              rw [V.δ_comp_σ_of_gt hji]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_comp_σ_castSucc_of_le i j hij := by
    -- Normalize the `Δ[1]` degeneracy to the next middle simplex, then use the fifth
    -- cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ.succ := by
      simpa using delta_one_sigma_objMk₁_of_le i j hij
    have hnat :
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ i.castSucc := by
      simpa [CosimplicialObject.σ, hmap] using
        (H.naturality (SimplexCategory.σ i.castSucc)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)).w
    have hEq :
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ ≫ V.σ i := by
      calc
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
            (U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ)) ≫ V.σ j := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ i.castSucc) ≫ V.σ j := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫
              (V.σ i.castSucc ≫ V.σ j) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫
              (V.σ j.succ ≫ V.σ i) := by
              rw [V.σ_comp_σ hij]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ ≫ V.σ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.σ] using hEq
  h_comp_σ_succ_of_lt i j hji := by
    -- Normalize the complementary `Δ[1]` degeneracy branch, then use the reversed fifth
    -- cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc := by
      simpa using delta_one_sigma_objMk₁_of_gt i j hji
    have hnat :
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ i.succ := by
      simpa [CosimplicialObject.σ, hmap] using
        (H.naturality (SimplexCategory.σ i.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)).w
    have hEq :
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ j.castSucc ≫ V.σ i := by
      calc
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
            (U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ)) ≫ V.σ j := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ i.succ) ≫ V.σ j := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              (V.σ i.succ ≫ V.σ j) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              (V.σ j.castSucc ≫ V.σ i) := by
              rw [← V.σ_comp_σ hji]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              V.σ j.castSucc ≫ V.σ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.σ] using hEq

private noncomputable def ofOppositeSimplicialHomotopyHom
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    ∀ n : ℕ, (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) → (U.obj ⦋n⦌ ⟶ V.obj ⦋n⦌) :=
  fun n α ↦
    match n with
    | 0 =>
        let i := (simplexIndexEquiv 0).symm α
        Fin.lastCases (a.app ⦋0⦌) (fun _ ↦ b.app ⦋0⦌) i
    | n + 1 =>
        let i := (simplexIndexEquiv (n + 1)).symm α
        Fin.lastCases
          (a.app ⦋n + 1⦌)
          (fun j ↦ Fin.cases
            (b.app ⦋n + 1⦌)
            (fun k ↦ (H.h k).unop ≫ V.δ k.castSucc)
            j)
          i

/-- Helper for Lemma 14.28.3: evaluating the reverse construction on the canonical simplex
`simplexIndexEquiv n k` reveals the endpoint/interior branch chosen by the `Fin` decomposition. -/
private lemma ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) (k : Fin (n + 2)) :
    ofOppositeSimplicialHomotopyHom H n (simplexIndexEquiv n k) =
      match n with
      | 0 =>
          Fin.lastCases (a.app ⦋0⦌) (fun _ ↦ b.app ⦋0⦌) k
      | n + 1 =>
          Fin.lastCases
            (a.app ⦋n + 1⦌)
            (fun j ↦ Fin.cases
              (b.app ⦋n + 1⦌)
              (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc)
              j)
            k := by
  cases n with
  | zero =>
      simp [ofOppositeSimplicialHomotopyHom, simplexIndexEquiv]
  | succ n =>
      simp [ofOppositeSimplicialHomotopyHom, simplexIndexEquiv]

/-- Helper for Lemma 14.28.3: the reverse component family defines a morphism property on
`SimplexCategory`; proving it on the generators is enough to recover the full naturality field. -/
private def reverseNaturalityProperty
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    MorphismProperty SimplexCategory :=
  fun _ _ θ ↦
    ∀ α, CommSq
      (U.map θ)
      (ofOppositeSimplicialHomotopyHom H _ (((Δ[1] : SSet.{0}).map θ.op α)))
      (ofOppositeSimplicialHomotopyHom H _ α)
      (V.map θ)

/-- Helper for Lemma 14.28.3: the reverse naturality predicate is multiplicative because
commutative squares compose horizontally. -/
private instance reverseNaturalityProperty_isMultiplicative
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    (reverseNaturalityProperty H).IsMultiplicative where
  id_mem n α := by
    -- For identities, both simplicial reindexing and the two object maps are identities.
    refine ⟨?_⟩
    simp
  comp_mem θ₁ θ₂ hθ₁ hθ₂ α := by
    -- For compositions, paste the two known commutative squares.
    simpa [reverseNaturalityProperty, Functor.map_comp] using
      CommSq.horiz_comp
        (hθ₁ (((Δ[1] : SSet.{0}).map θ₂.op α)))
        (hθ₂ α)

/-- Helper for Lemma 14.28.3: the reverse component family is natural with respect to face
generators of `SimplexCategory`. -/
private lemma reverse_component_naturality_delta
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 2)) :
    reverseNaturalityProperty H (SimplexCategory.δ i) := by
  intro α
  refine ⟨?_⟩
  obtain ⟨k, rfl⟩ := (simplexIndexEquiv (n + 1)).surjective α
  -- Reduce the square to the canonical `Fin`-indexed simplices in degree `n + 1`.
  refine Fin.lastCases ?_ ?_ k
  · -- TODO: identify the last simplex with the `a`-endpoint under `δ i`, then reduce the square
    -- to `a.naturality (SimplexCategory.δ i)` exactly as in the completed `σ`-endpoint branch.
    sorry
  · intro j
    refine Fin.cases ?_ ?_ j
    · -- The zero simplex is the `b`-endpoint, and faces preserve that endpoint.
      have hMap :
          ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
            (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3)))) =
            SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) := by
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n + 1)]
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n)]
        ext k : 1
        rfl
      have hLeft :
          ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
            b.app ⦋n + 1⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 1 (0 : Fin 3)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 2)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 4))) =
                  Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 2)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 4)) =
                  b.app ⦋n + 2⦌ := by
              change Fin.lastCases (a.app ⦋n + 2⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 2⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 2⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      have hRight :
          ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
            b.app ⦋n⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (0 : Fin 2)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 1)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
                  Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 3)) =
                  b.app ⦋n + 1⦌ := by
              change Fin.lastCases (a.app ⦋n + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
        b.naturality (SimplexCategory.δ i)
    · intro l
      by_cases hil : i ≤ l.castSucc
      · -- TODO: in the `i ≤ l.castSucc` branch, normalize the face of the interior simplex to the
        -- preceding canonical simplex and close with `H.h_succ_comp_δ_castSucc_of_lt`.
        sorry
      · by_cases hEq : i = l.succ
        · -- TODO: in the adjacent branch `i = l.succ`, rewrite both sides to the same middle
          -- simplex and close with `H.h_succ_comp_δ_castSucc_succ`.
          sorry
        · -- TODO: in the remaining branch `l.succ < i`, normalize to the following canonical
          -- simplex and close with `H.h_castSucc_comp_δ_succ_of_lt`.
          sorry

/-- Helper for Lemma 14.28.3: the reverse component family is natural with respect to degeneracy
generators of `SimplexCategory`. -/
private lemma reverse_component_naturality_sigma
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 1)) :
    reverseNaturalityProperty H (SimplexCategory.σ i) := by
  intro α
  refine ⟨?_⟩
  obtain ⟨k, rfl⟩ := (simplexIndexEquiv n).surjective α
  -- Reduce the square to the canonical `Fin`-indexed simplices in degree `n`.
  refine Fin.lastCases ?_ ?_ k
  · -- The last simplex is the `a`-endpoint, and degeneracies preserve that endpoint.
    have hMap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i).op
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)))) =
          SSet.stdSimplex.objMk₁ (Fin.last (n + 2)) := by
      rw [delta_one_map_objMk₁_sigma]
      rw [SSet.stdSimplex.σ_objMk₁_of_lt _ _]
      · simp
      · simpa using (Fin.castSucc_lt_last i)
    have hLeft :
        ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) =
          a.app ⦋n⦌ := by
      cases n with
      | zero =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (Fin.last 1)
      | succ n =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
              (Fin.last (n + 2))
    have hRight :
        ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (Fin.last (n + 2))) =
          a.app ⦋n + 1⦌ := by
      simpa [simplexIndexEquiv, Fin.lastCases_last] using
        ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1) (Fin.last (n + 2))
    simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
      a.naturality (SimplexCategory.σ i)
  · intro j
    refine Fin.cases ?_ ?_ j
    · -- The zero simplex is the `b`-endpoint, and degeneracies preserve that endpoint.
      have hMap :
          ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i).op
            (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)))) =
            SSet.stdSimplex.objMk₁ (0 : Fin (n + 3)) := by
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n)]
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n + 1)]
        ext k : 1
        rfl
      have hLeft :
          ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
            b.app ⦋n⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (0 : Fin 2)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 1)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
                  Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 3)) =
                  b.app ⦋n + 1⦌ := by
              change Fin.lastCases (a.app ⦋n + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      have hRight :
          ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
            b.app ⦋n + 1⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 1 (0 : Fin 3)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 2)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 4))) =
                  Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 2)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 4)) =
                  b.app ⦋n + 2⦌ := by
              change Fin.lastCases (a.app ⦋n + 2⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 2⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 2⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
        b.naturality (SimplexCategory.σ i)
    · intro l
      by_cases hil : i ≤ l.castSucc
      · -- TODO: in the `i ≤ l.castSucc` branch, rewrite the degeneracy of the interior simplex
        -- with `delta_one_sigma_objMk₁_of_le` and close with `H.h_comp_σ_castSucc_of_le`.
        sorry
      · have hli : l.castSucc < i := lt_of_not_ge hil
        -- TODO: in the complementary branch, rewrite with `delta_one_sigma_objMk₁_of_gt` and
        -- close with `H.h_comp_σ_succ_of_lt`.
        sorry

/-- Helper for Lemma 14.28.3: once the reverse component family is natural on the generators, it
is natural for every simplex operator. -/
private lemma reverse_component_naturality_all_simplex_maps
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n₁ n₂ : SimplexCategory} (θ : n₁ ⟶ n₂) :
    reverseNaturalityProperty H θ := by
  -- The generator proofs and multiplicativity upgrade the property to all simplex maps.
  have htop :
      reverseNaturalityProperty H = ⊤ :=
    SimplexCategory.morphismProperty_eq_top
      (reverseNaturalityProperty H)
      (fun {_} i ↦ reverse_component_naturality_delta H i)
      (fun {_} i ↦ reverse_component_naturality_sigma H i)
  simpa [htop]

-- Proof sketch: recover each simplex-indexed component by splitting `Δ[1]_n` via the canonical
-- bijection `SSet.stdSimplex.objMk₁ : Fin (n + 2) ≃ Δ[1]_n`; the two endpoints come from `a` and
-- `b`, and the interior simplices are obtained from the simplicial homotopy operators by the
-- appropriate target face map.
private def ofOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    DeltaOneHomotopy a b where
  hom {n} i := by
    cases n with
    | mk m =>
        exact ofOppositeSimplicialHomotopyHom H m i
  zero_endpoint n := by
    -- Normalize the endpoint simplex to the last canonical index and read off the `a` branch.
    cases n with
    | mk m =>
        rw [deltaOneZeroEndpoint_eq_objMk₁_last]
        cases m with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_last] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (Fin.last 1)
        | succ m =>
            simpa [simplexIndexEquiv, Fin.lastCases_last] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (m + 1) (Fin.last (m + 2))
  one_endpoint n := by
    -- Normalize the endpoint simplex to the zero canonical index and read off the `b` branch.
    cases n with
    | mk m =>
        rw [deltaOneOneEndpoint_eq_objMk₁_zero]
        cases m with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 0
        | succ m =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (m + 1) (SSet.stdSimplex.objMk₁ 0) =
                  Fin.lastCases (a.app ⦋m + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋m + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (m + 1) (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋m + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋m + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (m + 3)) =
                  b.app ⦋m + 1⦌ := by
              change Fin.lastCases (a.app ⦋m + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋m + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋m + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
  naturality σ i := by
    -- The reverse component family is natural on generators, hence on every simplex map.
    exact reverse_component_naturality_all_simplex_maps H σ i

/-- Helper for Lemma 14.28.3: the interior branch of the reverse-then-forward reconstruction
returns the original `Δ[1]`-indexed component. -/
private lemma forward_reverse_interior_reconstruction
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : DeltaOneHomotopy a b) {n : ℕ} (i : Fin (n + 1)) :
    (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).hom
        (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
      H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) := by
  -- TODO: expand the reverse construction on the canonical interior simplex, rewrite the extra
  -- `σ/δ` pair using the original `H.naturality (SimplexCategory.σ i)` square, and then collapse
  -- the remaining adjacent simplicial identity to recover the original component.
  sorry

private theorem ofOppositeSimplicialHomotopy_toOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H) = H := by
  -- Compare the two `Δ[1]`-indexed families on the canonical endpoint and interior simplices.
  apply DeltaOneHomotopy.ext
  intro n α
  cases n with
  | mk m =>
      obtain ⟨k, rfl⟩ := (simplexIndexEquiv m).surjective α
      cases m with
      | zero =>
          refine Fin.lastCases ?_ ?_ k
          · -- In degree `0`, the last canonical simplex is the constant `0` endpoint.
            simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using
              (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).zero_endpoint ⦋0⦌
                |>.trans (H.zero_endpoint ⦋0⦌).symm
          · intro j
            refine Fin.cases ?_ ?_ j
            · -- The zero canonical simplex is the constant `1` endpoint.
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using
                (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).one_endpoint ⦋0⦌
                  |>.trans (H.one_endpoint ⦋0⦌).symm
            · intro i
              exact Fin.elim0 i
      | succ m =>
          refine Fin.lastCases ?_ ?_ k
          · -- The last canonical simplex is the constant `0` endpoint.
            simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using
              (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).zero_endpoint
                  ⦋m + 1⦌
                |>.trans (H.zero_endpoint ⦋m + 1⦌).symm
          · intro j
            refine Fin.cases ?_ ?_ j
            · -- The zero canonical simplex is the constant `1` endpoint.
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using
                (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).one_endpoint
                    ⦋m + 1⦌
                  |>.trans (H.one_endpoint ⦋m + 1⦌).symm
            · intro i
              -- The remaining simplices are the canonical interior simplices.
              simpa using forward_reverse_interior_reconstruction (n := m) H i

private theorem toOppositeSimplicialHomotopy_ofOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    toOppositeSimplicialHomotopy (ofOppositeSimplicialHomotopy H) = H := by
  -- Extensionality reduces the comparison to the `h i` components.
  ext n i
  apply Quiver.Hom.unop_inj
  -- Evaluate the reverse construction on the canonical interior simplex and simplify with the
  -- adjacent `δσ = id` relation in the cosimplicial target.
  have hEval :
      (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
        (H.h i).unop ≫ V.δ i.castSucc := by
    calc
      (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
          Fin.lastCases
            (a.app ⦋n + 1⦌)
            (fun j ↦
              Fin.cases
                (b.app ⦋n + 1⦌)
                (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc)
                j)
            i.castSucc.succ := by
              simpa [ofOppositeSimplicialHomotopy, simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  i.succ.castSucc
      _ = (H.h i).unop ≫ V.δ i.castSucc := by
            rw [Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.cases_succ]
            rfl
  change (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫
      V.σ i =
    (H.h i).unop
  rw [hEval]
  simpa [toOppositeSimplicialHomotopy, Category.assoc] using
    (show ((H.h i).unop ≫ V.δ i.castSucc) ≫ V.σ i = (H.h i).unop by
      simpa [Category.assoc] using
        congrArg (fun k ↦ (H.h i).unop ≫ k) (V.δ_comp_σ_self (i := i)))

/-- Lemma 14.28.3: a `Δ[1]`-indexed homotopy from `a` to `b` between cosimplicial objects is
equivalent, at the level of actual homotopy data, to a simplicial homotopy between the
corresponding opposite morphisms `a', b' : V' ⟶ U'`. -/
def equivOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} (a b : U ⟶ V) :
    DeltaOneHomotopy a b ≃
      SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  toFun := toOppositeSimplicialHomotopy
  invFun := ofOppositeSimplicialHomotopy
  left_inv := ofOppositeSimplicialHomotopy_toOppositeSimplicialHomotopy
  right_inv := toOppositeSimplicialHomotopy_ofOppositeSimplicialHomotopy

end DeltaOneHomotopy

-- Proof sketch: this is the `Nonempty` companion of the data-level equivalence above.
-- Proof sketch: transport each generating step of the `Relation.EqvGen` closure across the
-- data-level equivalence above.
/-- The zigzag relation generated by `Δ[1]`-indexed cosimplicial homotopies agrees with the zigzag
relation generated by simplicial homotopies after passage to the opposite simplicial objects. -/
theorem deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
    {U V : CosimplicialObject C} (a b : U ⟶ V) :
    DeltaOneHomotopic a b ↔
      SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        exact SimplicialObject.Homotopic.of_homotopy
          (DeltaOneHomotopy.equivOppositeSimplicialHomotopy x y hxy.some)
    | refl x =>
        exact SimplicialObject.Homotopic.refl (NatTrans.op x)
    | symm x y _ ih =>
        exact ih.symm
    | trans x y z _ _ ihxy ihyz =>
        exact ihxy.trans ihyz
  · intro h
    have hunop :
        ∀ {x y : V.op ⟶ U.op}, SimplicialObject.Homotopic x y →
          DeltaOneHomotopic (NatTrans.unop x) (NatTrans.unop y) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
          exact DeltaOneHomotopic.of_homotopy <|
            (DeltaOneHomotopy.equivOppositeSimplicialHomotopy
              (NatTrans.unop x)
              (NatTrans.unop y)).symm <|
                by simpa using hxy.some
      | refl x =>
          exact DeltaOneHomotopic.refl (NatTrans.unop x)
      | symm x y _ ih =>
          exact ih.symm
      | trans x y z _ _ ihxy ihyz =>
          exact ihxy.trans ihyz
    simpa using hunop h

end CategoryTheory.CosimplicialObject

/-! ### Lemma_14_28_4 (from Chap14) -/
open CategoryTheory
open Opposite

universe u v u' v'

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.28.4:
- primary domain: simplicial and cosimplicial homotopy relations under functoriality and passage to
  opposites;
- sampled same-kind owner declarations:
  `CategoryTheory.SimplicialObject.Homotopic.whiskerRight`,
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic.whiskerRight`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`;
- best owner abstraction: the covariant functoriality statements are already owned by
  `SimplicialObject.Homotopic` and `CosimplicialObject.DeltaOneHomotopic`; the contravariant cases
  in this file are only bridge/view lemmas obtained by composing those owner theorems with the
  opposite-equivalence bridge from Lemma 14.28.3;
- primitive data: only the existing homotopy relation witness;
- derived API: contravariant transport via `NatTrans.unop` or `NatTrans.op`.

Source/core/bridge triage:
- `source-facing`: the four Stacks functoriality clauses;
- `core/canonical`: `SimplicialObject.Homotopic.whiskerRight` and
  `CosimplicialObject.DeltaOneHomotopic.whiskerRight`;
- `bridge/view`: the two contravariant-image clauses below, expressed through
  `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`. -/

/- Lemma 14.28.4 (1): a covariant functor sends homotopic morphisms of simplicial objects to
homotopic morphisms of the image simplicial objects. -/
recall SimplicialObject.Homotopic.whiskerRight
    {D : Type u} [Category.{v} D]
    {U V : SimplicialObject D} {a b : U ⟶ V}
    {D' : Type u'} [Category.{v'} D']
    (h : SimplicialObject.Homotopic a b)
    (F : D ⥤ D') :
  SimplicialObject.Homotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F)

/- Lemma 14.28.4 (2): a covariant functor sends `Δ[1]`-homotopic morphisms of cosimplicial
objects to `Δ[1]`-homotopic morphisms of the image cosimplicial objects. -/
recall CosimplicialObject.DeltaOneHomotopic.whiskerRight
    {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C']
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (h : CosimplicialObject.DeltaOneHomotopic a b)
    (F : C ⥤ C') :
  CosimplicialObject.DeltaOneHomotopic
    (Functor.whiskerRight a F)
    (Functor.whiskerRight b F)

-- Proof sketch: first whisker the simplicial zigzag along the contravariant functor viewed as a
-- covariant functor into `Cᵒᵖ`; this gives a zigzag of simplicial homotopies in `Cᵒᵖ`. Then apply
-- Lemma 14.28.3 backwards to convert that zigzag into a `Δ[1]`-homotopy zigzag of cosimplicial
-- morphisms in `C`.
section

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace SimplicialObject

variable {U V : SimplicialObject D} {a b : U ⟶ V}

/-- Lemma 14.28.4 (3): a contravariant functor sends homotopic morphisms of simplicial objects to
`Δ[1]`-homotopic morphisms of the associated image cosimplicial objects, reversing the direction
of the maps. This is a bridge/view lemma, not a second owner. -/
theorem Homotopic.contravariantMap
    (h : Homotopic a b) (F : D ⥤ Cᵒᵖ) :
    CosimplicialObject.DeltaOneHomotopic
      (NatTrans.unop (Functor.whiskerRight a F))
      (NatTrans.unop (Functor.whiskerRight b F)) := by
  simpa using
    (CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
      (NatTrans.unop (Functor.whiskerRight a F))
      (NatTrans.unop (Functor.whiskerRight b F))).2
      (h.whiskerRight F)

end SimplicialObject

-- Proof sketch: convert the given `Δ[1]`-homotopy zigzag to the opposite simplicial zigzag using
-- Lemma 14.28.3, apply the simplicial covariant functoriality statement to `F : Cᵒᵖ ⥤ D`, and
-- identify the resulting whiskered maps with the induced simplicial maps on the contravariant
-- images.
namespace CosimplicialObject

variable {U V : CosimplicialObject C} {a b : U ⟶ V}

/-- Lemma 14.28.4 (4): a contravariant functor sends `Δ[1]`-homotopic morphisms of cosimplicial
objects to homotopic morphisms of the associated image simplicial objects, reversing the direction
of the maps. This is a bridge/view lemma, not a second owner. -/
theorem DeltaOneHomotopic.contravariantMap
    (h : DeltaOneHomotopic a b) (F : Cᵒᵖ ⥤ D) :
    SimplicialObject.Homotopic
      (Functor.whiskerRight (NatTrans.op a) F)
      (Functor.whiskerRight (NatTrans.op b) F) := by
  simpa using
    ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h).whiskerRight F

end CosimplicialObject
end

end CategoryTheory
