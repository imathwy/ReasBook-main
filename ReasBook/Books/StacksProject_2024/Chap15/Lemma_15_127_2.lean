import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {R : Type u} [Ring R]
variable {ι : Type*} [Finite ι]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.127.2:
- primary domain: subcomplexes of a cochain complex of `R`-modules, together with the chapter
  owner for termwise finite-free complexes and the chapter style for arbitrary finite families;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `isMPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`;
- best owner abstraction:
  `source-facing`: a subcomplex `G ⊆ F` containing the chosen finite family of elements;
  `core/canonical`: the owner object `Subobject F`, with boundedness expressed by the ambient
    `IsStrictlyGE`/`IsStrictlyLE` predicates and finite freeness by
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: the inclusion morphism `G.arrow : (G : Cpx) ⟶ F`, whose degreewise components
    realize containment of the chosen elements;
- primitive vs. derived:
  the primitive datum is just the canonical subobject `G : Subobject F`;
  boundedness and termwise finite freeness are properties of the underlying complex and should not
  be repackaged as a parallel local structure, while the chosen finite family should be indexed by
  an arbitrary finite type `ι` rather than the coordinate model `Fin N`.
- layer: this file stays `source-facing`, but its theorem should quantify over `Subobject F`
  directly instead of introducing a duplicate wrapper owner, with the finite-family input kept at
  the weaker canonical `ι : Type*` / `[Finite ι]` abstraction level.
-/

-- Proof sketch: let `a` be the minimum of the finitely many prescribed degrees. Choose finitely
-- many basis vectors in degree `a` spanning the specified elements there, enlarge degree `a + 1`
-- by finitely many basis vectors containing their differentials, and then apply descending
-- induction on the lower bound to build a bounded finite free subcomplex containing every chosen
-- element.
/-- Lemma 15.127.2: a bounded above complex of free `R`-modules contains any finite family of
specified elements in a bounded finite free subcomplex. -/
theorem exists_bounded_finite_free_subcomplex_containing
    (F : Cpx)
    (hbounded : ∃ b : ℤ, F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i)) :
    ∃ G : Subobject F,
      (∃ a b : ℤ, (G : Cpx).IsStrictlyGE a ∧ (G : Cpx).IsStrictlyLE b) ∧
      (G : Cpx).IsTermwiseFiniteFree ∧
      ∀ i : ι,
        ∃ g : (G : Cpx).X (degrees i), G.arrow.f (degrees i) g = elements i :=
  sorry
