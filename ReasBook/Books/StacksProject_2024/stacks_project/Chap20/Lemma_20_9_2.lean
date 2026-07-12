import Mathlib.Topology.Sheaves.AddCommGrpCat

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} (ℱ : X.Presheaf AddCommGrpCat.{max u v})

namespace TopCat.Presheaf

/- Domain-style sampling for Lemma 20.9.2:
- primary domain: the degree-zero Čech sheaf criterion, expressed through compatible families and
  unique gluing on an open cover;
- sampled owner declarations:
  `TopCat.Presheaf.IsCompatible`,
  `TopCat.Presheaf.IsGluing`,
  `TopCat.Presheaf.IsSheafUniqueGluing`,
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`;
- source-facing layer: the degree-zero Čech criterion on a cover `U`, namely that the restriction
  map from sections on `iSup U` to compatible local families is bijective in the unique-gluing
  sense;
- core/canonical layer: the sheaf owners `ℱ.IsSheaf` and `ℱ.IsSheafUniqueGluing`, together with
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`;
- bridge/view: the concrete restriction family `restrictToCover` and the per-cover comparison
  theorem `isSheafUniqueGluing_iff_forall_cechZeroHasUniqueGluing`.
-/

/-- Restrict a section on `iSup U` to a family of sections on the members of the cover `U`. -/
def restrictToCover {ι : Type u} (U : ι → Opens X) (s : ℱ.obj (op (iSup U))) :
    ∀ i : ι, ℱ.obj (op (U i)) :=
  fun i ↦ ℱ.map (Opens.leSupr U i).op s

@[simp] theorem restrictToCover_apply {ι : Type u} (U : ι → Opens X)
    (s : ℱ.obj (op (iSup U))) (i : ι) :
    restrictToCover ℱ U s i = ℱ.map (Opens.leSupr U i).op s :=
  rfl

-- Proof sketch: both composites from `iSup U` to `U i ⊓ U j` factor through the same restriction
-- map, so the restricted family coming from a global section is compatible.
/-- Global sections restrict to a compatible family on any open covering. -/
theorem restrictToCover_isCompatible {ι : Type u} (U : ι → Opens X)
    (s : ℱ.obj (op (iSup U))) :
    IsCompatible ℱ U (restrictToCover ℱ U s) := by
  intro i j
  -- Both overlap restrictions are the same map from `U i ⊓ U j` into the union, because
  -- `Opens X` is a thin category.
  have hcomp :
      (U i).infLELeft (U j) ≫ Opens.leSupr U i =
        (U i).infLERight (U j) ≫ Opens.leSupr U j := by
    apply Subsingleton.elim
  -- Apply the presheaf to that common composite and rewrite the result back as nested
  -- restrictions from `iSup U` to the overlap.
  have hmap :
      CategoryTheory.ConcreteCategory.hom
          (ℱ.map (((U i).infLELeft (U j) ≫ Opens.leSupr U i).op)) s =
        CategoryTheory.ConcreteCategory.hom
          (ℱ.map (((U i).infLERight (U j) ≫ Opens.leSupr U j).op)) s :=
    congrArg (fun f : U i ⊓ U j ⟶ iSup U ↦ CategoryTheory.ConcreteCategory.hom (ℱ.map f.op) s)
      hcomp
  simpa [Functor.map_comp] using hmap

/-- Source-facing degree-zero Čech criterion for the cover `U`: every compatible local family
admits a unique gluing on `iSup U`. -/
def cechZeroHasUniqueGluing {ι : Type u} (U : ι → Opens X) : Prop :=
  ∀ sf : ∀ i : ι, ℱ.obj (op (U i)),
    IsCompatible ℱ U sf → ∃! s : ℱ.obj (op (iSup U)), IsGluing ℱ U sf s

/-- The canonical unique-gluing owner `ℱ.IsSheafUniqueGluing` is exactly the assertion that the
degree-zero Čech criterion holds for every open cover. -/
theorem isSheafUniqueGluing_iff_forall_cechZeroHasUniqueGluing :
    ℱ.IsSheafUniqueGluing ↔
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X), cechZeroHasUniqueGluing ℱ U :=
  Iff.rfl

-- Proof sketch: the forward implication is the canonical sheaf unique-gluing criterion. The
-- converse specializes the per-cover degree-zero Čech comparison criterion to the given
-- compatible family.
/-- Lemma 20.9.2: an abelian presheaf on `X` is a sheaf if and only if for every open covering,
the degree-zero Čech criterion holds, expressed here in the source-facing unique-gluing form
`cechZeroHasUniqueGluing ℱ U`. -/
@[stacks 01EG]
theorem isSheaf_iff_cechZeroHasUniqueGluing :
    ℱ.IsSheaf ↔
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X), cechZeroHasUniqueGluing ℱ U :=
  (isSheaf_iff_isSheafUniqueGluing ℱ).trans
    (isSheafUniqueGluing_iff_forall_cechZeroHasUniqueGluing ℱ)

end TopCat.Presheaf
