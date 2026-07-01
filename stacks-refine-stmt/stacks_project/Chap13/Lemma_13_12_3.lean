import Mathlib
import stacks_project.Chap13.Lemma_13_4_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex
open DerivedCategory

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.12.3:
- primary domain: distinguished triangles in the derived category attached to short exact
  sequences of cochain complexes, and their comparison with the degreewise-split owner triangles
  in the homotopy category after passage to the derived category;
- sampled owner declarations in this domain:
  `DerivedCategory.triangleOfSES`,
  `DerivedCategory.triangleOfSES_distinguished`,
  `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `Functor.mapTriangleCompIso`,
  `Functor.mapTriangleIso`,
  `DerivedCategory.quotientCompQhIso`;
- best owner abstraction: this item is a `bridge/view` statement. Its source-facing content is not
  a second owner of distinguished triangles, but the comparison between the canonical derived
  triangle `triangleOfSES hS` and the image under `Qh.mapTriangle` of the canonical homotopy
  triangle `CochainComplex.trianglehOfDegreewiseSplit S σ`; after transporting the latter along
  the canonical functor-composition isomorphisms to `Q.mapTriangle.obj
  (CochainComplex.triangleOfDegreewiseSplit S σ)`, the source-facing comparison is exactly the
  chapter owner theorem `exists_distinguished_triangle_unique_up_to_iso`;
- source/core/bridge triage:
  `source-facing`: the comparison between the derived triangle attached to the induced short exact
    sequence and the homotopy triangle attached to the same degreewise split short complex;
  `core/canonical`: `ShortComplex.Splitting.shortExact`,
    `shortExact_of_degreewise_shortExact`, `DerivedCategory.triangleOfSES`,
    `CochainComplex.trianglehOfDegreewiseSplit`, and
    `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`;
  `bridge/view`: the canonical transport of `Qh.mapTriangle.obj
    (CochainComplex.trianglehOfDegreewiseSplit S σ)` to
    `Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ)`.
- primitive data: a short complex `S` of cochain complexes and the degreewise splitting family
  `σ`;
- derived API: the induced short exactness proof
  `shortExact_of_degreewise_shortExact S (fun n ↦ (σ n).shortExact)`, the triangles
  `triangleOfSES ...`, `trianglehOfDegreewiseSplit S σ`, and
  `triangleOfDegreewiseSplit S σ`, together with the canonical triangle-comparison isomorphisms
  attached to `quotientCompQhIso` and the owner uniqueness theorem for distinguished triangles.
-/

-- Proof sketch: derive `S.ShortExact` from the degreewise splitting family. The triangle
-- `Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S σ)` is distinguished because
-- `trianglehOfDegreewiseSplit S σ` is distinguished in the homotopy category, and the canonical
-- `quotientCompQhIso` comparison transports it to the distinguished triangle
-- `Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ)`. Since this latter triangle
-- has the same first morphism as `triangleOfSES hS`, the chapter owner theorem
-- `exists_distinguished_triangle_unique_up_to_iso` gives the desired comparison in `D(𝒜)`.
/-- Lemma 13.12.3: for a degreewise split short complex of cochain complexes in an abelian
category, the distinguished triangle in `D(\mathcal A)` attached to the induced short exact
sequence is isomorphic to the image under `DerivedCategory.Qh` of the distinguished triangle in
`K(\mathcal A)` associated to the same degreewise split sequence. -/
theorem triangleOfSES_isomorphic_to_degreewiseSplitTriangleImage
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    IsIsomorphic
      (triangleOfSES
        (shortExact_of_degreewise_shortExact S fun n ↦ (σ n).shortExact))
      (Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S σ)) := by
  let hS : S.ShortExact :=
    shortExact_of_degreewise_shortExact S fun n ↦ (σ n).shortExact
  let eQ :
      Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S σ) ≅
        Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) :=
    (Functor.mapTriangleCompIso (HomotopyCategory.quotient 𝒜 (up ℤ)) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso 𝒜)).app _
  have hQ :
      Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) ∈
        distTriang (DerivedCategory 𝒜) := by
    refine isomorphic_distinguished
      (Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S σ)) ?_ _ eQ.symm
    apply Qh.map_distinguished
    rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
    exact ⟨S, σ, ⟨Iso.refl _⟩⟩
  obtain ⟨e, -, -⟩ :=
    exists_distinguished_triangle_unique_up_to_iso (triangleOfSES_distinguished hS) hQ
  exact ⟨e ≪≫ eQ.symm⟩

end CategoryTheory
