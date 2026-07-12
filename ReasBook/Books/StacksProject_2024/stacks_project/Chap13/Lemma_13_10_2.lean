import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open ComplexShape
open HomologicalComplex
open CochainComplex

universe v u

/- Source/core/bridge triage for Lemma 13.10.2:
- primary domain: termwise split short exact sequences of cochain complexes, their associated
  triangles in the homotopy category, and the octahedron axiom;
- inspected owner declarations:
  `ShortComplex`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `CategoryTheory.Triangulated.Octahedron`,
  `CategoryTheory.IsTriangulated.mk'`;
  from Definition 13.9.9, and the canonical homotopy-category triangles attached to them are the
  owner triangles `CochainComplex.trianglehOfDegreewiseSplit`; the octahedron datum should
  therefore be stated directly for the rows `ShortComplex.mk α p₁ hαp₁`,
  `ShortComplex.mk (α ≫ β) p₂ hαβp₂`, and `ShortComplex.mk β p₃ hβp₃`, not via extra
  existential short complexes that are immediately reidentified by equality proofs;
- layer:
  `source-facing`: the three short complexes attached to `α`, `β`, and `α ≫ β`, together with
    degreewise splitness;
  `core/canonical`: `ShortComplex`, `CochainComplex.trianglehOfDegreewiseSplit`, and
    `CategoryTheory.Triangulated.Octahedron`;
  `bridge/view`: the passage from the degreewise split rows to their owner triangles in the
    homotopy category;
- primitive data: the three third terms `Q₁`, `Q₂`, `Q₃`, the quotient maps
  `p₁ : B ⟶ Q₁`, `p₂ : C ⟶ Q₂`, `p₃ : C ⟶ Q₃`, their zero-composite relations with
  `α`, `α ≫ β`, and `β`, and the degreewise splitness existence conditions from
  Definition 13.9.9 for the associated rows `ShortComplex.mk α p₁ hαp₁`,
  `ShortComplex.mk (α ≫ β) p₂ hαβp₂`, and `ShortComplex.mk β p₃ hβp₃`;
- derived API: internal choices of splitting families, the connecting morphisms in the homotopy
  category, distinguishedness of the owner triangles, and the resulting octahedron datum.
-/

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

local notation "Q" => HomotopyCategory.quotient V (up ℤ)
local notation "K" => HomotopyCategory V (up ℤ)
section

variable {A B C X Y Z : CochainComplex V ℤ}

/- The only routine degreewise input needed later is that split monomorphisms compose
componentwise. We isolate that closure fact so the eventual octahedron proof can reuse it
without reopening the instance search argument in the main theorem. -/
/-- Helper for Lemma 13.10.2: termwise split monomorphisms of cochain complexes are closed under
composition. -/
lemma termwise_split_mono_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ n : ℤ, IsSplitMono (f.f n))
    (hg : ∀ n : ℤ, IsSplitMono (g.f n)) :
    ∀ n : ℤ, IsSplitMono ((f ≫ g).f n) := by
  intro n
  -- Each component map is a composition of split monomorphisms, hence split monic again.
  letI : IsSplitMono (f.f n) := hf n
  letI : IsSplitMono (g.f n) := hg n
  simpa using (show IsSplitMono (f.f n ≫ g.f n) from inferInstance)

/- Once a source-facing short complex is known to split after evaluation in every degree, its
owner triangle in the homotopy category is distinguished by the standard degreewise-split
characterization. This packages that bridge into a single reusable lemma. -/
/-- Helper for Lemma 13.10.2: the canonical triangle attached to a degreewise split short complex
of cochain complexes is distinguished in the homotopy category. -/
lemma triangle_mk_mem_distTriang_of_degreewise_split_short_complex
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    let T := trianglehOfDegreewiseSplit S σ
    Triangle.mk ((Q).map S.f) T.mor₂ T.mor₃ ∈ distTriang K := by
  let T := trianglehOfDegreewiseSplit S σ
  -- The bridge/view theorem identifies `T` with the standard owner triangle of `S`.
  simpa [T] using
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S, σ, ⟨Iso.refl _⟩⟩

-- Proof sketch: produce the three source-facing rows from Definition 13.9.9 attached to `α`,
-- `β`, and `α ≫ β`, together with chosen splitting families. These choices determine the
-- canonical owner triangles `CochainComplex.trianglehOfDegreewiseSplit` for the three rows.
-- Publicly, keep those owner triangles visible and state the octahedron datum directly for them,
-- rather than existentially repackaging their second and third morphisms.
/-- Lemma 13.10.2: if `α : A^• ⟶ B^•` and `β : B^• ⟶ C^•` are termwise split injections of
cochain complexes in an additive category, then there exist three source-facing short complexes
realizing the rows `0 ⟶ A^• ⟶ B^• ⟶ Q₁^• ⟶ 0`, `0 ⟶ A^• ⟶ C^• ⟶ Q₂^• ⟶ 0`, and
`0 ⟶ B^• ⟶ C^• ⟶ Q₃^• ⟶ 0`. Choosing splittings for these rows yields their canonical owner
triangles `trianglehOfDegreewiseSplit`, and these three owner triangles fit into an octahedron in
the homotopy category, expressing `TR4`. -/
theorem split_injections_of_cochain_complexes_have_octahedron
    {A B C : CochainComplex V ℤ} (α : A ⟶ B) (β : B ⟶ C)
    (hα : ∀ n : ℤ, IsSplitMono (α.f n)) (hβ : ∀ n : ℤ, IsSplitMono (β.f n)) :
    ∃ (Q₁ Q₂ Q₃ : CochainComplex V ℤ)
      (p₁ : B ⟶ Q₁) (hαp₁ : α ≫ p₁ = 0)
      (p₂ : C ⟶ Q₂) (hαβp₂ : (α ≫ β) ≫ p₂ = 0)
      (p₃ : C ⟶ Q₃) (hβp₃ : β ≫ p₃ = 0),
      (let S₁₂ := ShortComplex.mk α p₁ hαp₁
       let S₁₃ := ShortComplex.mk (α ≫ β) p₂ hαβp₂
       let S₂₃ := ShortComplex.mk β p₃ hβp₃
       ∃ (σ₁₂ : ∀ n : ℤ, (S₁₂.map (eval V (up ℤ) n)).Splitting)
         (σ₁₃ : ∀ n : ℤ, (S₁₃.map (eval V (up ℤ) n)).Splitting)
         (σ₂₃ : ∀ n : ℤ, (S₂₃.map (eval V (up ℤ) n)).Splitting),
         let T₁₂ := trianglehOfDegreewiseSplit S₁₂ σ₁₂
         let T₁₃ := trianglehOfDegreewiseSplit S₁₃ σ₁₃
         let T₂₃ := trianglehOfDegreewiseSplit S₂₃ σ₂₃
         ∃ (h₁₂ : Triangle.mk ((Q).map α) T₁₂.mor₂ T₁₂.mor₃ ∈ distTriang K)
           (h₂₃ : Triangle.mk ((Q).map β) T₂₃.mor₂ T₂₃.mor₃ ∈ distTriang K)
           (h₁₃ : Triangle.mk ((Q).map (α ≫ β)) T₁₃.mor₂ T₁₃.mor₃ ∈ distTriang K),
           Nonempty (Octahedron (Functor.map_comp Q α β).symm h₁₂ h₂₃ h₁₃)) := by
  -- Route correction: the ambient octahedron axiom already supplies the final `TR4` datum once
  -- the three source-facing rows `A ⟶ B ⟶ Q₁`, `A ⟶ C ⟶ Q₂`, and `B ⟶ C ⟶ Q₃` are available.
  -- The unresolved point is earlier: under the present assumptions we only know that each
  -- component `α.f n`, `β.f n`, and `(α ≫ β).f n` is split mono.
  -- TODO: a complete proof needs a source-level construction turning those componentwise split
  -- monomorphisms into actual cochain-level rows with maps `p₁`, `p₂`, and `p₃` whose evaluated
  -- short complexes admit splittings. Mathlib exposes complement decompositions for a split mono
  -- only after a cokernel is given, and the current hypotheses do not provide those cokernels.
  sorry

end
