import stacks_project.Chap06.Definition_6_3_2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens Topology
open scoped TopCat

universe u v

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

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type (max u v))]

/- Definition 6.7.4: the constant sheaf on `X` with value `A` is the canonical sheafification
of the constant presheaf, namely `CategoryTheory.constantSheaf`. -/
recall CategoryTheory.constantSheaf

private def constantToLocallyConstantPresheaf (A : Type (max u v)) :
    (A ₚ X) ⟶ locallyConstantPresheaf X A where
  app U a := ⟨fun _ ↦ a, IsLocallyConstant.const a⟩
  naturality {_ _} i := by
    rfl

/-- Definition 6.7.4 bridge: the canonical comparison from the constant sheaf with value `A` to
the source-facing sheaf of locally constant `A`-valued functions. -/
noncomputable def constantSheafToLocallyConstantSheaf (A : Type (max u v)) :
    (constantSheaf (Opens.grothendieckTopology X) (Type (max u v))).obj A ⟶
      locallyConstantSheaf X A :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (constantToLocallyConstantPresheaf X A)
      (locallyConstantPresheaf_isSheaf X A)⟩

/-- Definition 6.7.4 companion: the canonical comparison from the constant sheaf to the sheaf of
locally constant functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_isIso (A : Type (max u v)) :
    IsIso (constantSheafToLocallyConstantSheaf X A) := sorry

/-- Definition 6.7.4 companion: for every open `U ⊆ X`, the induced map on sections of the
canonical comparison from the constant sheaf with value `A` to the sheaf of locally constant
`A`-valued functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_app_isIso
    (A : Type (max u v)) (U : Opens X) :
    IsIso ((constantSheafToLocallyConstantSheaf X A).hom.app (op U)) := by
  letI := constantSheafToLocallyConstantSheaf_isIso X A
  letI :
      IsIso
        ((sheafToPresheaf (Opens.grothendieckTopology X) (Type (max u v))).map
          (constantSheafToLocallyConstantSheaf X A)) :=
    Functor.map_isIso _ (constantSheafToLocallyConstantSheaf X A)
  simpa using
    (show IsIso
      ((((sheafToPresheaf (Opens.grothendieckTopology X) (Type (max u v))).map
          (constantSheafToLocallyConstantSheaf X A)).app (op U))) by
      infer_instance)

end

end
