import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Sheaves.Sheaf
import StacksProject_2024.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.Sheaf.Torsor

/- Domain-style sampling for Definition 20.4.1:
- primary domain: sheaves of groups and torsors on a topological space;
- sampled owner declarations:
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.Hom`,
  `CategoryTheory.Sheaf.Torsor.trivial`,
  `CategoryTheory.Sheaf.Torsor.locallyNonempty`,
  `CategoryTheory.Sheaf.Torsor.Sections`,
  `CategoryTheory.Sheaf.Torsor.IsTrivial`;
- best owner abstraction: the canonical opens-site owner `CategoryTheory.Sheaf.Torsor G`;
- primitive data: exactly the site-level torsor data already owned by
  `CategoryTheory.Sheaf.Torsor G`, together with its canonical equivariant morphisms and
  distinguished trivial torsor;
- derived API: the reusable open-neighborhood bridge
  `exists_open_nhdsWithin_nonempty_sections` and the source-facing topological reformulation
  `locally_nonempty`, obtained by unpacking the covering-sieve field of the canonical owner in the
  opens-site case.

Primitive-vs-derived split:
- primitive data are the canonical owner `CategoryTheory.Sheaf.Torsor G`, its morphism type
  `CategoryTheory.Sheaf.Torsor.Hom`, and the canonical trivial torsor
  `CategoryTheory.Sheaf.Torsor.trivial G`;
- the pointwise neighborhood-language local nonemptiness in the textbook is derived from the
  owner's covering-sieve field on the opens site, so it should be exposed as a theorem rather than
  stored again as primitive data.

Source/core/bridge triage:
- `source-facing`: the Chapter 20 topological-space specialization of a sheaf torsor on the opens
  site, together with its morphisms and trivial object;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor G`;
- `bridge/view`: the morphism type `CategoryTheory.Sheaf.Torsor.Hom`, the trivial torsor
  `CategoryTheory.Sheaf.Torsor.trivial G`, and the within-open neighborhood bridge
  `exists_open_nhdsWithin_nonempty_sections` and the point-neighborhood reformulation
  `locally_nonempty` of the owner's covering-sieve field.
-/

variable {X : TopCat.{u}}
variable {G : X.Sheaf GrpCat.{u}}

/- Definition 20.4.1: for a sheaf of groups `G` on a topological space `X`, a `G`-torsor is the
canonical opens-site notion `CategoryTheory.Sheaf.Torsor G`. Morphisms of `G`-torsors are the
canonical equivariant sheaf maps `CategoryTheory.Sheaf.Torsor.Hom`, and the trivial `G`-torsor is
`CategoryTheory.Sheaf.Torsor.trivial G`. The textbook pointwise local-nonemptiness phrasing is
recovered below as a derived theorem. -/
#check (Torsor G)

/- Morphisms of `G`-torsors are the canonical equivariant morphisms of the site-level owner,
specialized here to the opens site of `X`. -/
#check (Torsor.Hom : Torsor G → Torsor G → Type _)

/- The trivial `G`-torsor on `X` is the canonical torsor obtained from `G` acting on itself by
left multiplication. -/
#check (trivial G : Torsor G)

/-- The trivial `G`-torsor has a canonical section over every open subset. -/
@[stacks 02FO]
theorem nonempty_sections_trivial (U : Opens X) :
    Nonempty ((trivial G).Sections U) :=
  by
    change Nonempty (((sheafForget (Opens.grothendieckTopology X)).obj G).1.obj (op U))
    exact ⟨(1 : G.1.obj (op U))⟩

/-- Any point of an open subset lies in a smaller open on which the torsor has a section. -/
theorem exists_open_nhdsWithin_nonempty_sections (P : Torsor G) (U : Opens X) {x : X}
    (hx : x ∈ U) :
    ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧ Nonempty (P.Sections V) := by
  rcases P.locallyNonempty U with ⟨S, hS_cover, hS_sections⟩
  rcases hS_cover x hx with ⟨V, f, hf, hxV⟩
  refine ⟨V, f.le, hxV, ?_⟩
  change Nonempty (P.carrier.1.obj (op V))
  exact hS_sections f hf

/-- Every point of `X` admits an open neighborhood carrying a section of a torsor. -/
@[stacks 02FO]
theorem locally_nonempty (P : Torsor G) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (P.Sections U) := by
  rcases exists_open_nhdsWithin_nonempty_sections P ⊤
      (show x ∈ (⊤ : Opens X) by trivial) with
    ⟨U, -, hxU, hU⟩
  exact ⟨U, hxU, hU⟩

end CategoryTheory.Sheaf.Torsor
