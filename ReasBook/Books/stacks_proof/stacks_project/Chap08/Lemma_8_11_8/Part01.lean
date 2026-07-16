import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part01.CanonicalAutomorphismSheaf

universe u v w uD vD

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Lemma 8.11.8 Part01: conjugation on the canonical abelian automorphism sheaves is
functorial under composition in a fiber. -/
@[stacks 0CJY]
theorem automorphismAddCommSheafConj_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext T α
  let F := canonicalFiberPseudofunctor 𝒮.p
  let eφ : x ≅ y := asIso φ
  let eψ : y ≅ z := asIso ψ
  let ecomp : x ≅ z := asIso (φ ≫ ψ)
  let pullbackFunctor := (F.map (.toLoc T.unop.hom.op)).toFunctor
  let Eφ := pullbackFunctor.mapIso eφ
  let Eψ := pullbackFunctor.mapIso eψ
  -- Pointwise, conjugation by a composite is the composite of the conjugations: `mapIso` of the
  -- composite iso splits (`Functor.mapIso_trans`), then `Iso.trans_conj` distributes.
  have hcomp : ecomp = eφ ≪≫ eψ := Iso.ext rfl
  change (pullbackFunctor.mapIso ecomp).conj α = Eψ.conj (Eφ.conj α)
  have hmap : pullbackFunctor.mapIso ecomp = Eφ ≪≫ Eψ := by
    -- Transport the composite fiber isomorphism through the restriction functor once.
    rw [hcomp]
    exact pullbackFunctor.mapIso_trans eφ eψ
  -- After the functoriality rewrite, the goal is the standard conjugation law for a transposed iso.
  rw [hmap]
  exact Iso.trans_conj Eφ Eψ α

/-- Helper for Lemma 8.11.8: parallel fiber morphisms induce the same conjugation isomorphism on
the canonical abelian automorphism sheaves. -/
theorem automorphismAddCommSheafConj_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
      automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  let eφ : x ≅ y := asIso φ
  let β : y ⟶ y := eφ.inv ≫ ψ
  have hfactor : φ ≫ β = ψ := by
    -- In a groupoid fiber, any parallel map differs by an inner automorphism of the target.
    dsimp [β, eφ]
    simp
  -- Abelianity kills the inner automorphism, so only the endpoints matter.
  rw [← hfactor, automorphismAddCommSheafConj_comp]
  simp [automorphism_addcomm_inner_conj_eq_refl]

/-- Helper for Lemma 8.11.8: after forgetting the additive structure, inner conjugation still
acts trivially on the underlying `Type`-valued automorphism sheaf. -/
theorem automorphismUnderlyingSheafConj_hom_self
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {z : 𝒮.p.Fiber U} (β : z ⟶ z) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian β = 𝟙 _ := by
  -- Forget the additive structure pointwise and reuse the abelian inner-conjugation collapse.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphism_addcomm_inner_conj_eq_refl (𝒮 := 𝒮) hAbelian β))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure preserves the composition law for
the canonical automorphism-sheaf conjugation maps. -/
theorem automorphismUnderlyingSheafConj_hom_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ ≫
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ψ := by
  -- Compare the underlying section maps pointwise after forgetting the additive structure.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphismAddCommSheafConj_comp (𝒮 := 𝒮) hAbelian φ ψ))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure preserves the fact that parallel
fiber morphisms induce the same conjugation map on automorphism sheaves. -/
theorem automorphismUnderlyingSheafConj_hom_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ =
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ψ := by
  -- The `Type`-valued overlap morphisms inherit independence of the chosen local isomorphism.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphismAddCommSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian φ ψ))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure on
`automorphismAddCommSheafConj` still produces an isomorphism of the underlying `Type`-valued
automorphism sheaves. This is the componentwise owner needed for the secondary-cover overlap
descent route. -/
noncomputable def automorphismUnderlyingSheafConj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y where
  hom := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ
  inv := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv
  hom_inv_id := by
    -- Conjugating by `φ` and then by `φ⁻¹` is an inner automorphism, hence trivial in the
    -- abelian automorphism sheaf.
    calc
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv
          =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (φ ≫ (asIso φ).inv) := by
            symm
            exact
              automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian φ (asIso φ).inv
      _ = 𝟙 _ := by
        exact
          automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian
            (φ ≫ (asIso φ).inv)
  inv_hom_id := by
    -- The reverse composite is the same inner-conjugation collapse on the target object.
    calc
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ
          =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ((asIso φ).inv ≫ φ) := by
            symm
            exact
              automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian (asIso φ).inv φ
      _ = 𝟙 _ := by
        exact
          automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian
            ((asIso φ).inv ≫ φ)

/-- Helper for Lemma 8.11.8: evaluating the underlying conjugation morphism for an isomorphism
class morphism gives the bare pointwise conjugation by `asIso`. -/
theorem automorphismUnderlyingSheafConj_hom_app_of_isIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) (hφ : IsIso φ) (T : (Over U)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj T) :
    ((automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ).1.app T) α =
      (((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso
        (@asIso _ _ _ _ φ hφ)).conj α := by
  -- With the chosen `IsIso` instance in scope, this is exactly the defining app of the map.
  letI : IsIso φ := hφ
  rfl

/-- Helper for Lemma 8.11.8: evaluating the underlying conjugation morphism associated to a
bundled fiber isomorphism gives the bare pointwise conjugation map. -/
theorem automorphismUnderlyingSheafConj_hom_app
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj T) :
    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom).hom.1.app T) α =
      (((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso e).conj
        α := by
  -- The definition uses `asIso e.hom`; identify it with the supplied bundled isomorphism.
  change (((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso
      (asIso e.hom)).conj α = _
  have he : asIso e.hom = e := by
    ext
    simp
  exact congrArg
    (fun i ↦
      (((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso i).conj
        α)
    he

/-- Helper for Lemma 8.11.8: the underlying `Type`-valued conjugation isomorphism is literally
the identity on endomorphisms, because abelianity kills inner conjugation. -/
theorem automorphismUnderlyingSheafConj_self
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {z : 𝒮.p.Fiber U} (β : z ⟶ z) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian β = Iso.refl _ := by
  apply Iso.ext
  -- The new iso-level API reduces immediately to the already-proved hom-level triviality.
  exact automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian β

/-- Helper for Lemma 8.11.8: the underlying `Type`-valued conjugation isomorphisms compose in the
same way as the additive conjugation isomorphisms from which they are forgotten. -/
theorem automorphismUnderlyingSheafConj_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  -- Equality of the underlying isomorphisms is checked on their `hom` fields.
  exact automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian φ ψ

/-- Helper for Lemma 8.11.8: on the underlying `Type`-valued automorphism sheaf, the induced
conjugation isomorphism depends only on the endpoints of a local isomorphism. -/
theorem automorphismUnderlyingSheafConj_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  -- This is the iso-level packaging of the previously proved hom-level endpoint-independence.
  exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian φ ψ

/-- Helper for Lemma 8.11.8: forgetting the additive structure on the canonical abelian
automorphism sheaf recovers the original `Type`-valued automorphism sheaf `Aut[𝒮](x)`. -/
noncomputable def automorphismUnderlyingSheafIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (x : 𝒮.p.Fiber U) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ≅ Aut[𝒮](x) := by
  let homNat :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1 ⟶ (Aut[𝒮](x)).1 :=
    { app := fun T α ↦ α
      naturality := by
        intro X Y g
        rfl }
  let invNat :
      (Aut[𝒮](x)).1 ⟶ (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1 :=
    { app := fun T α ↦ α
      naturality := by
        intro X Y g
        rfl }
  refine
    { hom := Sheaf.homEquiv.symm homNat
      inv := Sheaf.homEquiv.symm invNat
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sheaf.hom_ext
    ext T α
    rfl
  · apply Sheaf.hom_ext
    ext T α
    rfl

/-- Helper for Lemma 8.11.8: after identifying the forgotten abelian automorphism sheaf with
`Aut[𝒮](x)`, the forgotten conjugation isomorphism is the canonical `Type`-valued conjugation
isomorphism. -/
theorem automorphismUnderlyingSheafIso_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian x ≪≫
        automorphismSheafConj (𝒮 := 𝒮) φ =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y := by
  apply Iso.ext
  -- Both sides are pointwise the same conjugation map after forgetting the additive structure.
  apply Sheaf.hom_ext
  ext T α
  rfl

/-- Helper for Lemma 8.11.8 Part01: after forgetting the additive structure, the underlying
conjugation isomorphism still commutes with restriction along morphisms in a localized site. This
is the owner-level bridge from the canonical `Aut[𝒮]` naturality statement to the
`automorphismUnderlyingSheaf` API used on the secondary cover. -/
theorem automorphismUnderlyingSheafConj_pull_naturality
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (e : x ≅ y) {X Y : (Over U)ᵒᵖ} (g : X ⟶ Y)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj X) :
    let F := canonicalFiberPseudofunctor 𝒮.p
    ((F.map (Y.unop.hom.op.toLoc)).toFunctor.mapIso e).conj
      (pullHom α g.unop.left Y.unop.hom Y.unop.hom
        (by simpa using Over.w g.unop) (by simpa using Over.w g.unop)) =
    pullHom
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom).hom.1.app X) α)
      g.unop.left Y.unop.hom Y.unop.hom
      (by simpa using Over.w g.unop) (by simpa using Over.w g.unop) := by
  -- Reduce the wrapper statement to the canonical `Aut[𝒮]` naturality theorem; the only residual
  -- conversion is the pointwise computation of the forgotten conjugation map.
  convert automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e g α using 2
  rw [automorphismUnderlyingSheafConj_hom_app (𝒮 := 𝒮) hAbelian e X α]
  rfl

/-- Base-change coherence `θ` for the canonical automorphism sheaf: pulling the (Type-valued)
automorphism sheaf of `x` back along `q` agrees with the automorphism sheaf of the fibre pullback
`q ^* x`.  Concretely this is mathlib's `Pseudofunctor.overMapCompPresheafHomIso` for the
`canonicalFiberPseudofunctor` (the underlying presheaf of `automorphismUnderlyingSheaf x` is exactly
`presheafHom x x`, the `AddCommGrp ⋙ forget` round-trip being the identity on `Type`), lifted from
presheaves to sheaves through the fully faithful `sheafToPresheaf`. -/
noncomputable def automorphismUnderlyingSheafBaseChangeIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U) (x : 𝒮.p.Fiber U) :
    ((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x) :=
  (fullyFaithfulSheafToPresheaf (J.over Z) (Type (max u v))).preimageIso
    ((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q)

/-- Helper for Lemma 8.11.8: evaluating the hom side of the underlying automorphism
base-change isomorphism gives the hom component of the canonical presheaf comparison. -/
theorem automorphismUnderlyingSheafBaseChangeIso_hom_app
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U) (T : (Over Z)ᵒᵖ)
    (α : (((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj T) :
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app T) α =
      (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).hom.app T) α := by
  -- The sheaf isomorphism was defined by fully-faithful preimage from this presheaf isomorphism.
  rfl

/-- Helper for Lemma 8.11.8: evaluating the inverse side of the underlying automorphism
base-change isomorphism gives the inverse component of the canonical presheaf comparison. -/
theorem automorphismUnderlyingSheafBaseChangeIso_inv_app
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U) (T : (Over Z)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T) :
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv.1.app T) α =
      (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).inv.app T) α := by
  -- This is the inverse component of the same fully-faithful preimage construction.
  rfl

/-- Helper for Lemma 8.11.8: applying the hom-congruence equivalence from two isomorphisms
precomposes by the source inverse and postcomposes by the target hom. -/
theorem homFromEquiv_trans_homToEquiv_apply
    {D : Type*} [Category D] {A B X Y : D} (eA : A ≅ B) (eY : X ≅ Y)
    (f : A ⟶ X) :
    (eA.homFromEquiv.trans eY.homToEquiv) f = eA.inv ≫ f ≫ eY.hom := by
  -- This is the explicit morphism formula hidden inside the bundled equivalence.
  simp [Iso.homFromEquiv, Iso.homToEquiv, Category.assoc]

/-- Helper for Lemma 8.11.8: applying the inverse of the hom-congruence equivalence from two
isomorphisms precomposes by the source hom and postcomposes by the target inverse. -/
theorem homFromEquiv_trans_homToEquiv_symm_apply
    {D : Type*} [Category D] {A B X Y : D} (eA : A ≅ B) (eY : X ≅ Y)
    (f : B ⟶ Y) :
    ((eA.homFromEquiv.trans eY.homToEquiv).symm) f = eA.hom ≫ f ≫ eY.inv := by
  -- The inverse equivalence is definitionally this conjugation on hom sets.
  rfl

/-- Helper for Lemma 8.11.8: a sevenfold composition can be re-associated around the middle
conjugation factor. -/
theorem reassoc_conjugation_middle {D : Type*} [Category D]
    {A B C D₁ E F G H : D} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D₁)
    (d : D₁ ⟶ E) (e : E ⟶ F) (f : F ⟶ G) (g : G ⟶ H) :
    (a ≫ b ≫ c) ≫ d ≫ e ≫ f ≫ g = a ≫ (b ≫ (c ≫ d ≫ e) ≫ f) ≫ g := by
  -- Normalize both long composites to the same right-associated form.
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: conjugating a composite by an isomorphism distributes across the
two factors. -/
theorem iso_inv_hom_comp_comp {D : Type uD} [Category.{vD} D]
    {A B : D} (e : A ≅ B) (α β : A ⟶ A) :
    e.inv ≫ (α ≫ β) ≫ e.hom =
      (e.inv ≫ α ≫ e.hom) ≫ (e.inv ≫ β ≫ e.hom) := by
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: the hom component of the canonical presheaf base-change
comparison is precomposition by the inverse `mapComp'` cell and postcomposition by its hom cell. -/
theorem overMapCompPresheafHomIso_hom_app {U Z : C} {x y : 𝒮.p.Fiber U}
    (q : Z ⟶ U) (T : (Over Z)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor 𝒮.p).presheafHom x y).obj
      (op ((Over.map q).obj T.unop))) :
    (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x y q).hom.app T) α =
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).inv.toNatTrans.app x ≫
        α ≫
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).hom.toNatTrans.app y := by
  -- Unfold the bundled hom-set equivalence once and name the comparison cell that it uses.
  let κ := (canonicalFiberPseudofunctor 𝒮.p).mapComp'
    q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Iso.homFromEquiv, Iso.homToEquiv,
    Equiv.trans]
  change ((fun f ↦ f ≫ κ.hom.toNatTrans.app y)
      ((fun f ↦ κ.inv.toNatTrans.app x ≫ f) α)) =
    κ.inv.toNatTrans.app x ≫ α ≫ κ.hom.toNatTrans.app y
  beta_reduce
  rw [Category.assoc]
  rfl

/-- Helper for Lemma 8.11.8: the inverse component of the canonical presheaf base-change
comparison is precomposition by the hom `mapComp'` cell and postcomposition by its inverse cell. -/
theorem overMapCompPresheafHomIso_inv_app {U Z : C} {x y : 𝒮.p.Fiber U}
    (q : Z ⟶ U) (T : (Over Z)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor 𝒮.p).presheafHom
      (((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc).toFunctor.obj x)
      (((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc).toFunctor.obj y)).obj T) :
    (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x y q).inv.app T) α =
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).hom.toNatTrans.app x ≫
        α ≫
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).inv.toNatTrans.app y := by
  -- The inverse side is the same unfolded equivalence with the hom and inverse cells swapped.
  let κ := (canonicalFiberPseudofunctor 𝒮.p).mapComp'
    q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Iso.homFromEquiv, Iso.homToEquiv,
    Equiv.trans]
  change ((fun f ↦ κ.hom.toNatTrans.app x ≫ f)
      ((fun f ↦ f ≫ κ.inv.toNatTrans.app y) α)) =
    κ.hom.toNatTrans.app x ≫ α ≫ κ.inv.toNatTrans.app y
  beta_reduce
  rfl

/-- Helper for Lemma 8.11.8: the hom side of the canonical automorphism base-change
isomorphism preserves the abelian-group addition on automorphism sections. -/
theorem automorphismUnderlyingSheafBaseChangeIso_hom_map_add
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U) (T : (Over Z)ᵒᵖ)
    (α β : (((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj T) :
    letI : AddCommGroup ((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj T) := by
      change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj
        (op ((Over.map q).obj T.unop)))
      infer_instance
    letI : AddCommGroup ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T) := by
      change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T)
      infer_instance
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app T) (α + β) =
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app T) α +
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app T) β := by
  dsimp
  change
    (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).hom.app T)
        (α ≫ β) =
      ((((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).hom.app T) α) ≫
        ((((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).hom.app T) β)
  rw [overMapCompPresheafHomIso_hom_app]
  rw [overMapCompPresheafHomIso_hom_app]
  rw [overMapCompPresheafHomIso_hom_app]
  let κ := (canonicalFiberPseudofunctor 𝒮.p).mapComp'
    q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl
  change κ.inv.toNatTrans.app x ≫ (α ≫ β) ≫ κ.hom.toNatTrans.app x =
    (κ.inv.toNatTrans.app x ≫ α ≫ κ.hom.toNatTrans.app x) ≫
      (κ.inv.toNatTrans.app x ≫ β ≫ κ.hom.toNatTrans.app x)
  let A := ((canonicalFiberPseudofunctor 𝒮.p).map
    (q.op.toLoc ≫ T.unop.hom.op.toLoc)).toFunctor.obj x
  let B := ((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc ≫
    (canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.obj x
  let e : A ≅ B := (Cat.Hom.toNatIso κ).app x
  change e.inv ≫ ((show A ⟶ A from α) ≫ (show A ⟶ A from β)) ≫ e.hom =
    (e.inv ≫ (show A ⟶ A from α) ≫ e.hom) ≫
      (e.inv ≫ (show A ⟶ A from β) ≫ e.hom)
  exact iso_inv_hom_comp_comp e (show A ⟶ A from α) (show A ⟶ A from β)

/-- Helper for Lemma 8.11.8: the inverse side of the canonical automorphism base-change
isomorphism preserves the abelian-group addition on automorphism sections. -/
theorem automorphismUnderlyingSheafBaseChangeIso_inv_map_add
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U) (T : (Over Z)ᵒᵖ)
    (α β : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T) :
    letI : AddCommGroup ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T) := by
      change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x)).1.obj T)
      infer_instance
    letI : AddCommGroup ((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj T) := by
      change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj
        (op ((Over.map q).obj T.unop)))
      infer_instance
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv.1.app T) (α + β) =
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv.1.app T) α +
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv.1.app T) β := by
  dsimp
  change
    (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).inv.app T)
        (α ≫ β) =
      ((((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).inv.app T) α) ≫
        ((((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).inv.app T) β)
  rw [overMapCompPresheafHomIso_inv_app]
  rw [overMapCompPresheafHomIso_inv_app]
  rw [overMapCompPresheafHomIso_inv_app]
  let κ := (canonicalFiberPseudofunctor 𝒮.p).mapComp'
    q.op.toLoc T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl
  change κ.hom.toNatTrans.app x ≫ (α ≫ β) ≫ κ.inv.toNatTrans.app x =
    (κ.hom.toNatTrans.app x ≫ α ≫ κ.inv.toNatTrans.app x) ≫
      (κ.hom.toNatTrans.app x ≫ β ≫ κ.inv.toNatTrans.app x)
  let A := ((canonicalFiberPseudofunctor 𝒮.p).map
    (q.op.toLoc ≫ T.unop.hom.op.toLoc)).toFunctor.obj x
  let B := ((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc ≫
    (canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.obj x
  let e : A ≅ B := (Cat.Hom.toNatIso κ).app x
  change e.hom ≫ ((show B ⟶ B from α) ≫ (show B ⟶ B from β)) ≫ e.inv =
    (e.hom ≫ (show B ⟶ B from α) ≫ e.inv) ≫
      (e.hom ≫ (show B ⟶ B from β) ≫ e.inv)
  exact iso_inv_hom_comp_comp e.symm (show B ⟶ B from α) (show B ⟶ B from β)

/-- Helper for Lemma 8.11.8: the canonical base-change comparison for automorphism presheaves
intertwines conjugation with the conjugation by the pulled-back fiber isomorphism. -/
theorem overMapCompPresheafHomIso_conj_app
    {U Z : C} {x y : 𝒮.p.Fiber U} (q : Z ⟶ U) (e : x ≅ y)
    (T : (Over Z)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor 𝒮.p).presheafHom x x).obj
      (op ((Over.map q).obj T.unop))) :
    (((canonicalFiberPseudofunctor 𝒮.p).map
        ((Over.map q).obj T.unop).hom.op.toLoc).toFunctor.mapIso e).conj α =
      (((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso y y q).inv.app T)
        ((((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso
          (((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc).toFunctor.mapIso e)).conj
          ((((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q).hom.app T)
            α)) := by
  -- Expose the comparison maps pointwise; their flanking `mapComp'` cells cancel by naturality.
  rw [Iso.conj_apply, Iso.conj_apply]
  simp only [Functor.mapIso_hom, Functor.mapIso_inv]
  rw [overMapCompPresheafHomIso_hom_app, overMapCompPresheafHomIso_inv_app]
  have hinv :=
    (canonicalFiberPseudofunctor 𝒮.p).mapComp'_naturality_2 q.op.toLoc
      T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl e.inv
  have hhom :=
    (canonicalFiberPseudofunctor 𝒮.p).mapComp'_naturality_2 q.op.toLoc
      T.unop.hom.op.toLoc (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl e.hom
  -- After the two naturality rewrites, the remaining goal is only associativity.
  erw [← hinv, ← hhom]
  exact reassoc_conjugation_middle _ _ _ _ _ _ _

/-- Helper for Lemma 8.11.8 Part01: pulling back the underlying conjugation morphism along `q`
is exactly conjugation by the pulled fiber isomorphism over `Z`. This is the thin transport
adapter needed when the source route reaches a pulled conjugation shell. -/
theorem automorphismUnderlyingSheafConj_pullbackFunctor_map
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x y : 𝒮.p.Fiber U} (q : Z ⟶ U) (φ : x ⟶ y) :
    ((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).mapIso
            (asIso φ)).hom)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q y).inv := by
  -- Pulling the conjugation `conj φ` back along `q` is, through the base-change coherence `θ`,
  -- conjugation by the pulled fibre isomorphism over `Z`.  We first strip away the sheaf wrappers
  -- pointwise, then use the presheaf-level base-change conjugation lemma.
  apply Sheaf.hom_ext
  ext T α
  simp only [automorphismUnderlyingSheafConj,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map_hom_app,
    Functor.mapIso_hom, asIso_hom]
  rw [automorphismUnderlyingSheafConj_hom_app_of_isIso (𝒮 := 𝒮) (hAbelian := hAbelian) φ
    (inferInstance : IsIso φ)]
  change _ = ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q y).inv.1.app T)
    (((automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ)).1.app T)
      (((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app T) α))
  rw [automorphismUnderlyingSheafBaseChangeIso_hom_app]
  rw [automorphismUnderlyingSheafConj_hom_app_of_isIso (𝒮 := 𝒮) (hAbelian := hAbelian)
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ)
    (inferInstance : IsIso (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ))]
  rw [automorphismUnderlyingSheafBaseChangeIso_inv_app]
  have hpullIso :
      ((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso
          (asIso (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ)) =
        ((canonicalFiberPseudofunctor 𝒮.p).map T.unop.hom.op.toLoc).toFunctor.mapIso
          (((canonicalFiberPseudofunctor 𝒮.p).map q.op.toLoc).toFunctor.mapIso
            (@asIso (𝒮.p.Fiber U) _ x y φ (inferInstance : IsIso φ))) := by
    -- The canonical pullback functor is the `q`-component of the fiber pseudofunctor.
    congr 1
    ext
    rfl
  rw [hpullIso]
  simpa using overMapCompPresheafHomIso_conj_app (𝒮 := 𝒮) q
    (@asIso (𝒮.p.Fiber U) _ x y φ (inferInstance : IsIso φ)) T α

/-- A sheaf `G` of abelian groups is a band for the gerbe `𝒮` if its restriction to every
localized site `C/U` identifies, as a sheaf of abelian groups, with the
canonical abelian-group automorphism sheaf attached to each object `x` of the fiber over `U`, and
these identifications are compatible with canonical conjugation by morphisms in that fiber. -/
def IsGerbeBand (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
    ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison y

/-- Helper for Lemma 8.11.8: fix once and for all one gerbe cover of each object of the base. -/
noncomputable def chosen_gerbe_cover
    (hGerbe : IsGerbe J 𝒮.p) (U : C) : J.Cover U :=
  Classical.choose (hGerbe.locally_inhabited U)

/-- Helper for Lemma 8.11.8: for the fixed chosen gerbe cover of `U`, choose one local object on
each cover arrow. -/
noncomputable def chosen_gerbe_cover_object
    (hGerbe : IsGerbe J 𝒮.p) (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    𝒮.p.Fiber I.Y :=
  Classical.choice ((Classical.choose_spec (hGerbe.locally_inhabited U)) I)

/-- Helper for Lemma 8.11.8: for any two objects in one fiber, use the covering sieve of all
arrows over which they become isomorphic. This is the source-faithful local owner for overlap
comparisons, and unlike an arbitrary chosen subcover it is stable under further pullback. -/
noncomputable def chosen_local_isomorphism_cover
    (hGerbe : IsGerbe J 𝒮.p) {U : C} (x y : 𝒮.p.Fiber U) : J.Cover U :=
  let hc := canonicalPullbackChoice 𝒮.p
  let R : Sieve U :=
    { arrows := fun {Y} f ↦ Nonempty (f ^*[hc] x ≅ f ^*[hc] y)
      downward_closed := by
        intro Y Z f hf g
        rcases hf with ⟨e⟩
        exact ⟨
          (hc.pullbackCompComponentIso f g x) ≪≫
            (hc.pullbackFunctor g).mapIso e ≪≫
              (hc.pullbackCompComponentIso f g y).symm⟩ }
  let S₀ := Classical.choose (hGerbe.locally_isomorphic x y)
  have hS₀R : (S₀ : Sieve U) ≤ R := by
    intro Y f hf
    exact Classical.choose_spec (hGerbe.locally_isomorphic x y) ⟨Y, f, hf⟩
  ⟨R, J.superset_covering hS₀R S₀.condition⟩

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover, choose one local comparison
isomorphism between the two pulled-back fiber objects. -/
noncomputable def chosen_local_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U : C} (x y : 𝒮.p.Fiber U)
    (I : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x y).Arrow) :
    I.f ^*[canonicalPullbackChoice 𝒮.p] x ≅
      I.f ^*[canonicalPullbackChoice 𝒮.p] y :=
  Classical.choice I.hf

/-- Helper for Lemma 8.11.8: on an overlap object of the fixed chosen cover, pull back the first
chosen local object to that overlap. This isolates the source proof's first local owner. -/
noncomputable abbrev local_overlap_source_object
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ : S.Arrow} (f₁ : Y ⟶ I₁.Y) :
    𝒮.p.Fiber Y :=
  f₁ ^*[canonicalPullbackChoice 𝒮.p] xS I₁

/-- Helper for Lemma 8.11.8: on the same overlap object, pull back the second chosen local
object. The source proof compares automorphism sheaves of these two overlap objects. -/
noncomputable abbrev local_overlap_target_object
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₂ : S.Arrow} (f₂ : Y ⟶ I₂.Y) :
    𝒮.p.Fiber Y :=
  f₂ ^*[canonicalPullbackChoice 𝒮.p] xS I₂

/-- Helper for Lemma 8.11.8: once the two local overlap objects are fixed, choose the secondary
cover on which they become isomorphic. This is the source-faithful owner for the overlap descent
step. -/
noncomputable abbrev local_overlap_isomorphism_cover
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    J.Cover Y :=
  chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
    (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)

/-- Helper for Lemma 8.11.8: on the chosen secondary cover of an overlap object, pick the local
isomorphism between the two pulled-back cover objects. -/
noncomputable def local_overlap_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) :=
  chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
    (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
    (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)
    K

/-- Helper for Lemma 8.11.8: because the local-isomorphism cover is the maximal covering sieve
of arrows with an isomorphism witness, an arrow of the pulled-leg overlap cover is also an arrow
of the original overlap cover after composing with the pullback map. -/
noncomputable def local_overlap_isomorphism_cover_comp_arrow
    (hGerbe : IsGerbe J 𝒮.p) {U Y' Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow :=
  let hc := canonicalPullbackChoice 𝒮.p
  { Y := K.Y
    f := K.f ≫ g
    hf := by
      rcases K.hf with ⟨e⟩
      let sourceIso :
          (K.f ≫ g) ^*[hc] (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
            K.f ^*[hc] (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁) :=
        (hc.pullbackCompComponentIso f₁ (K.f ≫ g) (xS I₁)).symm ≪≫
          eqToIso (by simp [local_overlap_source_object, Category.assoc, hgf₁]) ≪≫
            hc.pullbackCompComponentIso gf₁ K.f (xS I₁)
      let targetIso :
          (K.f ≫ g) ^*[hc] (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) ≅
            K.f ^*[hc] (local_overlap_target_object (𝒮 := 𝒮) S xS gf₂) :=
        (hc.pullbackCompComponentIso f₂ (K.f ≫ g) (xS I₂)).symm ≪≫
          eqToIso (by simp [local_overlap_target_object, Category.assoc, hgf₂]) ≪≫
            hc.pullbackCompComponentIso gf₂ K.f (xS I₂)
      exact ⟨sourceIso ≪≫ e ≪≫ targetIso.symm⟩ }

/-- Helper for Lemma 8.11.8: each chosen local isomorphism on the secondary overlap cover induces
the corresponding local conjugation isomorphism on the underlying automorphism sheaves. -/
noncomputable def local_overlap_conjugation_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)) :=
  -- The source proof's local comparison on the secondary cover is exactly conjugation by the
  -- chosen local isomorphism.
  automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K).hom

/-- Helper for Lemma 8.11.8: first pull the source automorphism sheaf from the fixed chosen cover
to the overlap object `Y`. This names the source sheaf before the secondary-cover descent step,
so later overlap proofs do not have to reopen the outer pullback shell. -/
noncomputable abbrev local_overlap_source_secondary_sheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ : S.Arrow} (f₁ : Y ⟶ I₁.Y) :
    Sheaf (J.over Y) (Type (max u v)) :=
  ((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.obj
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))

/-- Helper for Lemma 8.11.8: pull the target automorphism sheaf from the fixed chosen cover to the
same overlap object `Y`, mirroring `local_overlap_source_secondary_sheaf` on the target side. -/
noncomputable abbrev local_overlap_target_secondary_sheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₂ : S.Arrow} (f₂ : Y ⟶ I₂.Y) :
    Sheaf (J.over Y) (Type (max u v)) :=
  ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.obj
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))

/-- Helper for Lemma 8.11.8: package the source sheaf on the overlap object as a descent datum on
the chosen secondary cover. This isolates the source side of the remaining `isoMk` square as a
concrete object of the descent-data category. -/
noncomputable abbrev local_overlap_source_secondary_descent_data
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f) :=
  (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f)).obj
    (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁))

/-- Helper for Lemma 8.11.8: package the target sheaf on the overlap object as a descent datum on
the same chosen secondary cover. With both sides named, the remaining blocker is a single
secondary-cover descent isomorphism rather than a repeated transport shell. -/
noncomputable abbrev local_overlap_target_secondary_descent_data
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f) :=
  (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f)).obj
    (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂))

/-- Helper for Lemma 8.11.8: the `isoMk` square for the chosen local conjugation family
normalizes to the common pairwise-pullback conjugation map on the secondary cover. -/
theorem local_overlap_source_secondary_transition_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg₂)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) := by
  -- This descent datum is literally `toDescentData` applied to the source sheaf over `Y`.
  rfl

/-- Helper for Lemma 8.11.8: the target-side secondary-cover descent transition is the canonical
`toDescentData` comparison between the two pullback legs to the common owner `q`. -/
theorem local_overlap_target_secondary_transition_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    (local_overlap_target_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg₂)).hom.toNatTrans.app
          (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) := by
  -- The target descent datum is the same `toDescentData` owner applied to the target sheaf.
  rfl

/-- Helper for Lemma 8.11.8: the source object pulled back to the common owner `q` is identified
with the iterated pullback through one arrow of the secondary overlap cover. -/
noncomputable abbrev local_overlap_common_owner_source_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫
    hc.pullbackCompComponentIso K.f g
      (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)

/-- Helper for Lemma 8.11.8: the target object pulled back to the common owner `q` is identified
with the iterated pullback through the same secondary-cover arrow. -/
noncomputable abbrev local_overlap_common_owner_target_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫
    hc.pullbackCompComponentIso K.f g
      (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)

/-- Helper for Lemma 8.11.8: one local comparison isomorphism on the secondary overlap cover can
be rewritten as an isomorphism between the common-owner pullbacks along `q`. -/
noncomputable abbrev local_overlap_common_owner_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) :=
  let hc := canonicalPullbackChoice 𝒮.p
  local_overlap_common_owner_source_iso (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg ≪≫
    (hc.pullbackFunctor g).mapIso
      (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K) ≪≫
    (local_overlap_common_owner_target_iso (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).symm

/-- Helper for Lemma 8.11.8: after rewriting the common-owner leg by `hg`, the inverse
`mapComp'` component of the canonical fiber pseudofunctor is exactly the inverse source-side
common-owner comparison isomorphism. This is the fiber-level half of the blocked sectionwise
transport normalization. -/
theorem local_overlap_common_owner_source_iso_inv_eq_mapComp'_inv_app
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).inv.toNatTrans.app
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) =
      (local_overlap_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv := by
  -- Route correction: reduce the flexible `mapComp'` shell to the canonical pullback-composition
  -- comparison after substituting the common-owner equality `hg`.
  cases hg
  simpa [local_overlap_common_owner_source_iso] using
    (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
      (hc := canonicalPullbackChoice 𝒮.p) K.f g
      (local_overlap_source_object (𝒮 := 𝒮) S xS f₁))

/-- Helper for Lemma 8.11.8: after rewriting the common-owner leg by `hg`, the hom `mapComp'`
component of the canonical fiber pseudofunctor is exactly the hom target-side common-owner
comparison isomorphism. This is the symmetric fiber-level transport normalization needed later on
the target half of the overlap square. -/
theorem local_overlap_common_owner_target_iso_hom_eq_mapComp'_hom_app
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).hom.toNatTrans.app
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) =
      (local_overlap_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom := by
  -- The target-side common-owner comparison is the hom-side version of the same canonical
  -- pullback-composition package.
  cases hg
  simpa [local_overlap_common_owner_target_iso] using
    (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
      (hc := canonicalPullbackChoice 𝒮.p) K.f g
      (local_overlap_target_object (𝒮 := 𝒮) S xS f₂))

/-- Helper for Lemma 8.11.8 Part01: after both local overlap maps are rewritten to the same common owner
`q`, abelianity makes their induced conjugation maps equal because they are parallel morphisms. -/
theorem local_overlap_common_owner_conjugation_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom := by
  -- Both rewritten overlap isomorphisms have the same source and target over `q`, so the
  -- endpoint-independence lemma for conjugation applies directly.
  simpa using
    automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      (local_overlap_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom
      (local_overlap_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom

end CategoryTheory
