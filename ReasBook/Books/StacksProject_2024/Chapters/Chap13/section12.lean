import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_12_1 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.12.1:
- primary domain: connecting morphisms for short exact sequences of cochain complexes in the
  derived category;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `DerivedCategory.triangleOfSESδ`,
  `DerivedCategory.triangleOfSES_distinguished`,
  `DerivedCategory.triangleOfSESδ_naturality`;
- best owner abstraction: the source-facing item is the canonical `DeltaFunctor` structure on the
  functor `Comp(𝒜) ⥤ D(𝒜)`;
- source/core/bridge triage:
  `source-facing`: the canonical `δ`-functor on cochain complexes valued in the derived category;
  `core/canonical`: `DerivedCategory.Q` together with the owner declarations
    `triangleOfSESδ`, `triangleOfSES_distinguished`, and `triangleOfSESδ_naturality`;
  `bridge/view`: the `DeltaFunctor` packaging from `Definition_13_3_6`, which collects exactly the
    connecting morphisms, distinguished triangles, and naturality squares required by the source.

Primitive data are only the underlying functor `DerivedCategory.Q` and the owner-level connecting
morphisms for short exact sequences. The distinguished-triangle and naturality statements are
derived API from these owners, so this file should expose the canonical `DeltaFunctor` rather than
re-package those facts as a conjunction theorem.
-/

-- Proof sketch: take the connecting morphisms to be `DerivedCategory.triangleOfSESδ hS`. The
-- associated distinguished-triangle and naturality fields are exactly the canonical owner lemmas
-- `DerivedCategory.triangleOfSES_distinguished hS` and
-- `DerivedCategory.triangleOfSESδ_naturality hS hS' φ`.
/-- Lemma 13.12.1: the canonical functor
`\mathrm{Comp}(\mathcal A)=\mathrm{CoCh}(\mathcal A) \to D(\mathcal A)` carries the canonical
connecting morphisms attached to short exact sequences of cochain complexes, making it into a
`δ`-functor. -/
noncomputable def cochainComplexToDerivedDeltaFunctor :
    DeltaFunctor (Comp(𝒜)) (D(𝒜)) where
  toFunctor := Q
  additive := inferInstance
  δ := fun {_} hS ↦ triangleOfSESδ hS
  map_distinguished := fun {_} hS ↦ triangleOfSES_distinguished hS
  δ_naturality := fun {_ _} hS hS' φ ↦
    ⟨(triangleOfSESδ_naturality hS hS' φ).symm⟩

end CategoryTheory

/-! ### Lemma_13_12_2 (from Chap13) -/
open CategoryTheory.Pretriangulated
open DerivedCategory
open HomologicalComplex.HomologySequence

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.12.2:
- primary domain: distinguished triangles in the derived category attached to short exact
  sequences of cochain complexes, together with morphisms induced by maps of short exact
  sequences;
- sampled owner declarations in this domain:
  `DerivedCategory.triangleOfSES`,
  `DerivedCategory.triangleOfSES.map`,
  `HomologicalComplex.HomologySequence.quasiIso_τ₃`,
  `Pretriangulated.Triangle.isIso_of_isIsos`,
  `DerivedCategory.Q`'s instance sending a quasi-isomorphism to an isomorphism;
- best owner abstraction: the core owner is the canonical triangle morphism
  `DerivedCategory.triangleOfSES.map`; its being an isomorphism is derived API from the three
  component morphisms and the ambient triangle-category lemma `Triangle.isIso_of_isIsos`;
- source/core/bridge triage:
  `source-facing`: the induced morphism between the two distinguished triangles attached to the
    short exact sequences;
  `core/canonical`: `triangleOfSES.map` together with `Triangle.isIso_of_isIsos` and the
    localization functor `DerivedCategory.Q`;
  `bridge/view`: none beyond the canonical passage from quasi-isomorphisms of cochain complexes to
    isomorphisms after applying `Q`.

Primitive data are only the short exact sequences, the morphism `φ`, and the quasi-isomorphism
assumptions on `φ.τ₁` and `φ.τ₂`. The third quasi-isomorphism is already derived by the canonical
owner lemma `HomologicalComplex.HomologySequence.quasiIso_τ₃`, and the fact that the induced
triangle morphism is an isomorphism is derived from those owner-level data, so no auxiliary
wrapper or second triangle-level API should be introduced here.
-/

-- Proof sketch: derive `QuasiIso φ.τ₃` from `hτ₁` and `hτ₂` using
-- `HomologicalComplex.HomologySequence.quasiIso_τ₃`. The three components of
-- `triangleOfSES.map hS hT φ` are then `Q.map φ.τ₁`, `Q.map φ.τ₂`, and `Q.map φ.τ₃`, so
-- `Triangle.isIso_of_isIsos` applies directly to the canonical triangle morphism.
/- Companion recall: for a morphism of short exact sequences of cochain complexes, if the first
two vertical maps are quasi-isomorphisms, then the third vertical map is the canonical owner
consequence `quasiIso_τ₃`. -/
recall quasiIso_τ₃

/-- Lemma 13.12.2: a morphism between short exact sequences of cochain complexes whose first two
vertical maps are quasi-isomorphisms induces an isomorphism between the associated distinguished
triangles in the derived category; the third vertical map is automatically a quasi-isomorphism. -/
theorem triangleOfSES_map_isIso_of_quasiIso
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (hτ₁ : QuasiIso φ.τ₁) (hτ₂ : QuasiIso φ.τ₂) :
    IsIso (triangleOfSES.map hS hT φ) := by
  letI : QuasiIso φ.τ₁ := hτ₁
  letI : QuasiIso φ.τ₂ := hτ₂
  letI : QuasiIso φ.τ₃ := quasiIso_τ₃ φ hS hT hτ₁ hτ₂
  refine Triangle.isIso_of_isIsos (triangleOfSES.map hS hT φ) ?_ ?_ ?_
  all_goals
    simpa [triangleOfSES.map] using (inferInstance : IsIso _)

end CategoryTheory

/-! ### Lemma_13_12_3 (from Chap13) -/
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

/-! ### Remark_13_12_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

universe w v u

noncomputable section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Remark 13.12.4:
- primary domain: the canonical `t`-structure on `DerivedCategory 𝒜` and its truncation triangles;
- sampled owner declarations:
  `DerivedCategory.TStructure.t`,
  `CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished`,
  `CategoryTheory.Triangulated.TStructure.natTransTruncLEOfLE`,
  `CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE`,
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the primitive data are the owner truncation functors
  `t.truncLE`, `t.truncGE`, their canonical maps, and the owner distinguished triangle
  `t.triangleLEGE_distinguished`; the single-degree object in parts `(2)` and `(3)` is the
  canonical homology term `singleFunctor 𝒜 n ((H n).obj K)`, identified via the owner
  `singleFunctorCompHomologyFunctorIso`, not by a parallel local wrapper or an anonymous chosen
  witness;
- source/core/bridge triage:
  part `(1)` is `core/canonical`, so it should be a direct owner use rather than a renamed local
    theorem;
  parts `(2)` and `(3)` are `bridge/view` statements from the owner truncation triangles to the
    source-facing successive-truncation triangles whose third/first term is identified with a
    homology object in one degree.
- primitive-vs-derived split: the truncation functors, transition maps, and distinguished
  truncation triangle are primitive owner data; the successive-truncation triangles with homology
  terms are derived/source-facing API.
-/

section

variable (K : DerivedCategory 𝒜) (a : ℤ)

/- Remark 13.12.4 (1): for every `K ∈ D(\mathcal A)` and `a ∈ \mathbf Z`, the canonical
truncations fit into the distinguished triangle
`\tau_{\le a}K^\bullet \to K^\bullet \to \tau_{\ge a+1}K^\bullet \to
(\tau_{\le a}K^\bullet)[1]`. This is exactly the canonical owner triangle
`t.triangleLEGE_distinguished` specialized to `DerivedCategory 𝒜`. -/
#check
  (t.triangleLEGE_distinguished a (a + 1) rfl K :
    (t.triangleLEGE a (a + 1) rfl).obj K ∈ distTriang (DerivedCategory 𝒜))

end

private theorem isIso_homologyMap_truncGEπ
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n).map T.mor₂))

private theorem isIso_homologyMap_truncLTι
    (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) := by
  subst h
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE (n₀ + 1)).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished (n₀ + 1) K
  have h₃ : T.obj₃.IsGE (n₀ + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    letI := h₃
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    letI := h₃
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n₀).map T.mor₁))

private instance (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) :=
  isIso_homologyMap_truncGEπ K n

private instance (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) :=
  isIso_homologyMap_truncLTι K n₀ n₁ h

private instance (K : DerivedCategory 𝒜) (a b : ℤ) (h : b ≤ a) :
    IsIso ((t.truncGE a).map ((t.truncGEπ b).app K)) :=
  t.isIso_truncGE_map_truncGEπ_app a b h K

private noncomputable def singleFunctorIsoOfIsGEOfIsLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) := by
  classical
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  exact e ≪≫ (singleFunctor 𝒜 n).mapIso eH.symm

-- Proof sketch: the owner step triangle is `t.triangleLTLTGELT`; the bridge data are the
-- canonical homology isomorphism for the concentrated third term and the induced isomorphism of
-- triangles.
/-- Remark 13.12.4 (2): the degree-`a+1` cohomology piece extracted from the successive upper
truncations carries the same cohomology as `K` in degree `a+1`. -/
noncomputable def truncLE_step_homologyIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (H (a + 1)).obj K :=
  by
  let eπ :
      (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅
        (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) :=
    asIso ((H (a + 1)).map ((t.truncGEπ (a + 1)).app ((t.truncLT (a + 2)).obj K)))
  let eι : (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅ (H (a + 1)).obj K :=
    asIso ((H (a + 1)).map ((t.truncLTι (a + 2)).app K))
  exact eπ.symm ≪≫ eι

/-- Remark 13.12.4 (2): the concentrated degree-`a+1` truncation piece is canonically the single
object on `H^{a+1}(K^\bullet)`. -/
noncomputable def truncLE_step_termIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (singleFunctor 𝒜 (a + 1)).obj ((H (a + 1)).obj K) := by
  have h : (a + 2) - 1 = a + 1 := by omega
  haveI : ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE (a + 1) := by
    simpa [h] using
      (inferInstance :
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE ((a + 2) - 1))
  exact
    singleFunctorIsoOfIsGEOfIsLE
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) (a + 1) ≪≫
      (singleFunctor 𝒜 (a + 1)).mapIso (truncLE_step_homologyIso K a)

/-- Remark 13.12.4 (2), bridge/view form: the successive upper truncations of `K` fit into the
distinguished triangle whose third object is the cohomology term `H^{a+1}(K^\bullet)[-a-1]`. -/
noncomputable def truncLE_step_homologyTriangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle (DerivedCategory 𝒜) :=
  Triangle.mk
    ((t.natTransTruncLTOfLE (a + 1) (a + 2) (by omega)).app K)
    (((Functor.whiskerLeft (t.truncLT (a + 2)) (t.truncGEπ (a + 1))).app K) ≫
      (truncLE_step_termIso K a).hom)
    ((truncLE_step_termIso K a).inv ≫ (t.truncGELTδLT (a + 1) (a + 2)).app K)

/-- The source-facing upper-step triangle is canonically isomorphic to the owner triangle
`(t.triangleLTLTGELT (a+1) (a+2)).obj K`. -/
private noncomputable def truncLE_step_homologyTriangleIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle K a ≅
      (t.triangleLTLTGELT (a + 1) (a + 2) (by omega)).obj K := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (truncLE_step_termIso K a).symm ?_ ?_ ?_
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]

/-- Remark 13.12.4 (2): the successive upper truncations of `K` and the degree-`a+1` cohomology
object of `K` form a distinguished triangle. -/
theorem truncLE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle K a ∈ distTriang (DerivedCategory 𝒜) :=
  isomorphic_distinguished _ (t.triangleLTLTGELT_distinguished (a + 1) (a + 2) (by omega) K) _
    (truncLE_step_homologyTriangleIso K a)

-- Proof sketch: the owner step triangle is `t.triangleLTGE (a+1)` applied to `\tau_{\ge a}K`;
-- the bridge data are the canonical homology isomorphism for the concentrated first term and the
-- canonical identification of the third term with `\tau_{\ge a+1}K`.
/-- Remark 13.12.4 (3): the degree-`a` cohomology piece extracted from the successive lower
truncations carries the same cohomology as `K` in degree `a`. -/
noncomputable def truncGE_step_homologyIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ (H a).obj K :=
  by
  let eι :
      (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
        (H a).obj ((t.truncGE a).obj K) :=
    asIso ((H a).map ((t.truncLTι (a + 1)).app ((t.truncGE a).obj K)))
  let eπ : (H a).obj K ≅ (H a).obj ((t.truncGE a).obj K) :=
    asIso ((H a).map ((t.truncGEπ a).app K))
  exact eι ≪≫ eπ.symm

/-- Remark 13.12.4 (3): the concentrated degree-`a` truncation piece is canonically the single
object on `H^a(K^\bullet)`. -/
noncomputable def truncGE_step_termIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
      (singleFunctor 𝒜 a).obj ((H a).obj K) := by
  haveI : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE a := by
    simpa using
      (inferInstance : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE ((a + 1) - 1))
  exact
    singleFunctorIsoOfIsGEOfIsLE
        ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) a ≪≫
      (singleFunctor 𝒜 a).mapIso (truncGE_step_homologyIso K a)

/-- Remark 13.12.4 (3), bridge/view form: the successive lower truncations of `K` fit into the
distinguished triangle whose first object is the cohomology term `H^a(K^\bullet)[-a]`. -/
noncomputable def truncGE_step_homologyTriangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle (DerivedCategory 𝒜) :=
  Triangle.mk
    ((truncGE_step_termIso K a).inv ≫ (t.truncLTι (a + 1)).app ((t.truncGE a).obj K))
    ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app K)
    (((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) ≫
      (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj K) ≫ ((truncGE_step_termIso K a).hom)⟦1⟧')

/-- The source-facing lower-step triangle is canonically isomorphic to the owner triangle
`(t.triangleLTGE (a+1)).obj ((t.truncGE a).obj K)`. -/
private noncomputable def truncGE_step_homologyTriangleIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncGE_step_homologyTriangle K a ≅
      (t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K) := by
  let e₃ : (t.truncGE (a + 1)).obj K ≅ (t.truncGE (a + 1)).obj ((t.truncGE a).obj K) :=
    asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))
  refine Triangle.isoMk _ _ (truncGE_step_termIso K a).symm (Iso.refl _) e₃ ?_ ?_ ?_
  · simp [truncGE_step_homologyTriangle]
  · haveI : ((t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K)).obj₃.IsGE a := by
      dsimp
      exact t.isGE_of_ge _ a (a + 1) (by omega)
    exact t.from_truncGE_obj_ext (by
      simpa [truncGE_step_homologyTriangle, e₃, Category.assoc, t.π_natTransTruncGEOfLE_app] using
        (NatTrans.naturality (t.truncGEπ (a + 1)) ((t.truncGEπ a).app K)).symm)
  · have he₃ : e₃.hom = (t.truncGE (a + 1)).map ((t.truncGEπ a).app K) := by
      change (asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app K))).hom =
        (t.truncGE (a + 1)).map ((t.truncGEπ a).app K)
      simp
    simp [truncGE_step_homologyTriangle, he₃, Category.assoc]

/-- Remark 13.12.4 (3): the degree-`a` cohomology object of `K` and the successive lower
truncations of `K` form a distinguished triangle. -/
theorem truncGE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncGE_step_homologyTriangle K a ∈ distTriang (DerivedCategory 𝒜) :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished (a + 1) ((t.truncGE a).obj K)) _
    (truncGE_step_homologyTriangleIso K a)

end

/-! ### Lemma_13_12_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Lemma 13.12.5:
- primary domain: truncation factorization in the canonical `t`-structure on `D(\mathcal A)`,
  with stepwise vanishing measured by the derived-category homology functors;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.homologyFunctor`,
  `TStructure.liftTruncLE`,
  `TStructure.descTruncGE`,
  `t.truncLEι`,
  `t.truncGEπ`;
- best owner abstraction: the source-facing data are already a chain in `DerivedCategory 𝒜`,
  whose endpoint boundedness belongs to the canonical owners `S.left.IsLE 0` and
  `S.right.IsGE 0`; the degreewise vanishing of the induced homology maps remains explicit
  primitive data, but now at the same owner layer;
- primitive data: the composable-arrow diagram `S : ComposableArrows (DerivedCategory 𝒜) n` and
  the vanishing of the degree `-j` or `j` homology-functor maps for its successive arrows
  `S.arrow j`;
- derived API: existence of a factorization through the canonical truncation maps
  `τ_{\le -n}(S.right) ⟶ S.right` and `S.left ⟶ τ_{\ge n}(S.left)`;
- source/core/bridge triage:
  `source-facing`: the two factorization theorems below;
  `core/canonical`: the owners `DerivedCategory.IsLE` / `IsGE`, the homology functors `H i`,
    and the truncation morphisms `t.truncLEι`, `t.truncGEπ`;
  `bridge/view`: `DerivedCategory.isLE_iff` / `isGE_iff`, translating the textbook cohomology
    vanishing conditions into those owner predicates.

Accordingly, this file keeps the two source-facing factorization theorems, upgrades only the
public surface from chosen cochain-complex representatives to the intrinsic derived-category
objects and deletes the redundant complex-level wrapper surface.
-/

-- Proof sketch: argue by induction on the length of the composable-arrow diagram. The case
-- `n = 1` comes from the distinguished truncation triangle of Remark 13.12.4 and the vanishing
-- of the induced map on degree-`0` homology; the induction step factors first through
-- `τ_{\le -(n-1)}` of the penultimate complex and then applies the case `n = 1` to the induced
-- map between successive truncations.
/-- Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose source is `≤ 0`
(equivalently, has no positive cohomology) and whose degree-`-j` homology-functor maps vanish at
each step, then the total composite factors through the canonical truncation map
`τ_{\le -n}(Kₙ) ⟶ Kₙ`. -/
theorem exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.left.IsLE 0)
    (hstep : ∀ j (hj : j < n), (H (-(j : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : S.left ⟶ (t.truncLE (-(n : ℤ))).obj S.right,
      φ ≫ (t.truncLEι (-(n : ℤ))).app S.right = S.hom := sorry

-- Proof sketch: apply the previous induction argument to the dual truncation triangles. The base
-- case `n = 1` uses the distinguished triangle for `τ_{\ge 1}`, and the induction step factors
-- successively through `τ_{\ge j}` because each degree-`j` homology map is zero.
/-- Dual form of Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose target is
`≥ 0` (equivalently, has no negative cohomology) and whose degree-`j` homology-functor maps
vanish at each step, then the total composite factors through the canonical map
`K₀ ⟶ τ_{\ge n}(K₀)`. -/
theorem exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.right.IsGE 0)
    (hstep : ∀ j (hj : j < n), (H (j : ℤ)).map (S.arrow j hj).hom = 0) :
    ∃ φ : (t.truncGE (n : ℤ)).obj S.left ⟶ S.right,
      (t.truncGEπ (n : ℤ)).app S.left ≫ φ = S.hom := sorry

end CategoryTheory
