import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Remark 13.12.4 (1): the canonical truncations of `K` fit into the owner distinguished
triangle `τ_{\le a}K ⟶ K ⟶ τ_{\ge a + 1}K ⟶ (τ_{\le a}K)[1]`. -/
@[stacks 08J5]
theorem truncation_triangle_distinguished :
    (t.triangleLEGE a (a + 1) rfl).obj K ∈ distTriang (DerivedCategory 𝒜) := by
  -- Proof comment: this is exactly the canonical truncation triangle from the owner t-structure.
  simpa using
    (t.triangleLEGE_distinguished a (a + 1) rfl K :
      (t.triangleLEGE a (a + 1) rfl).obj K ∈ distTriang (DerivedCategory 𝒜))

end

/-- Helper for Remark 13.12.4: the lower truncation projection induces an isomorphism on the
surviving degree-`n` homology. -/
private theorem isIso_homologyMap_truncGEπ
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  -- Proof comment: the left truncation piece has no degree-`n` or degree-`n+1` homology.
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n).map T.mor₂))

/-- Helper for Remark 13.12.4: the upper truncation inclusion induces an isomorphism on the
last surviving degree-`n₀` homology. -/
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
  -- Proof comment: the right truncation piece has no degree-`n₀` or degree-`n₀-1` homology.
  have hmor₂_zero : (H n₀).map T.mor₂ = 0 := by
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) n₀ (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (n₀ - 1) n₀ (by omega) = 0 := by
    exact (isZero_of_isGE T.obj₃ (n₀ + 1) (n₀ - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H n₀).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).2 hmor₂_zero
  letI : Mono ((H n₀).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (n₀ - 1) n₀ (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H n₀).map T.mor₁))

/-- Helper for Remark 13.12.4: use the projection comparison as an instance. -/
private instance (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) :=
  isIso_homologyMap_truncGEπ K n

/-- Helper for Remark 13.12.4: use the inclusion comparison as an instance. -/
private instance (K : DerivedCategory 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((H n₀).map ((t.truncLTι n₁).app K)) :=
  isIso_homologyMap_truncLTι K n₀ n₁ h

/-- Helper for Remark 13.12.4: further lower truncation of `τ_{\ge b} K` is already an
isomorphism once `b ≤ a`. -/
private instance (K : DerivedCategory 𝒜) (a b : ℤ) (h : b ≤ a) :
    IsIso ((t.truncGE a).map ((t.truncGEπ b).app K)) :=
  t.isIso_truncGE_map_truncGEπ_app a b h K

/-- Helper for Remark 13.12.4: an object concentrated in degree `n` is canonically the single
object on its degree-`n` homology. -/
private noncomputable def singleFunctorIsoOfIsGEOfIsLE
    (X : DerivedCategory 𝒜) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor 𝒜 n).obj ((H n).obj X) := by
  classical
  let hX := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (singleFunctor 𝒜 n).obj Y := Classical.choice (Classical.choose_spec hX)
  let eH : (H n).obj X ≅ Y :=
    (H n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso 𝒜 n).app Y
  -- Proof comment: replace the chosen concentrated model by the canonical one indexed by `H^n(X)`.
  exact e ≪≫ (singleFunctor 𝒜 n).mapIso eH.symm

-- Proof sketch: the owner step triangle is `t.triangleLTLTGELT`; the bridge data are the
-- canonical homology isomorphism for the concentrated third term and the induced isomorphism of
-- triangles.
/-- Remark 13.12.4 (2): the degree-`a+1` cohomology piece extracted from the successive upper
truncations carries the same cohomology as `K` in degree `a+1`. -/
@[stacks 08J5]
noncomputable def truncLE_step_homologyIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (H (a + 1)).obj K := by
  let eπ :
      (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅
        (H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) :=
    @asIso _ _ _ _
      ((H (a + 1)).map ((t.truncGEπ (a + 1)).app ((t.truncLT (a + 2)).obj K)))
      (isIso_homologyMap_truncGEπ (𝒜 := 𝒜) ((t.truncLT (a + 2)).obj K) (a + 1))
  let eι : (H (a + 1)).obj ((t.truncLT (a + 2)).obj K) ≅ (H (a + 1)).obj K :=
    @asIso _ _ _ _
      ((H (a + 1)).map ((t.truncLTι (a + 2)).app K))
      (isIso_homologyMap_truncLTι (𝒜 := 𝒜) K (a + 1) (a + 2) (by omega))
  -- Proof comment: compare first with the concentrated truncation piece and then with `K`.
  exact eπ.symm ≪≫ eι

/-- Remark 13.12.4 (2): the concentrated degree-`a+1` truncation piece is canonically the single
object on `H^{a+1}(K^\bullet)`. -/
@[stacks 08J5]
noncomputable def truncLE_step_termIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
      (singleFunctor 𝒜 (a + 1)).obj ((H (a + 1)).obj K) := by
  have h : (a + 2) - 1 = a + 1 := by
    omega
  have hLE : ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE (a + 1) := by
    simpa [h] using
      (inferInstance :
        ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)).IsLE ((a + 2) - 1))
  letI := hLE
  let e :
      ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) ≅
        (singleFunctor 𝒜 (a + 1)).obj
          ((H (a + 1)).obj ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K))) :=
    singleFunctorIsoOfIsGEOfIsLE
      ((t.truncGE (a + 1)).obj ((t.truncLT (a + 2)).obj K)) (a + 1)
  -- Proof comment: the step object is concentrated in degree `a + 1`, so it is the single object
  -- on its own degree-`a+1` homology, which was identified above with `H^{a+1}(K)`.
  exact e ≪≫ (singleFunctor 𝒜 (a + 1)).mapIso (truncLE_step_homologyIso K a)

/-- Remark 13.12.4 (2), bridge/view form: the successive upper truncations of `K` fit into the
distinguished triangle whose third object is the cohomology term `H^{a+1}(K^\bullet)[-a-1]`. -/
@[stacks 08J5]
noncomputable def truncLE_step_homologyTriangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle (DerivedCategory 𝒜) :=
  Triangle.mk
    ((t.natTransTruncLTOfLE (a + 1) (a + 2) (by omega)).app K)
    (((Functor.whiskerLeft (t.truncLT (a + 2)) (t.truncGEπ (a + 1))).app K) ≫
      (truncLE_step_termIso K a).hom)
    ((truncLE_step_termIso K a).inv ≫ (t.truncGELTδLT (a + 1) (a + 2)).app K)

/-- Helper for Remark 13.12.4: the source-facing upper-step triangle is isomorphic to the owner
truncation triangle. -/
private noncomputable def truncLE_step_homologyTriangleIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle K a ≅
      (t.triangleLTLTGELT (a + 1) (a + 2) (by omega)).obj K := by
  -- Proof comment: the only difference from the owner triangle is the replacement of the third
  -- vertex by the canonical homology-model isomorphism.
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (truncLE_step_termIso K a).symm ?_ ?_ ?_
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]
  · simp [truncLE_step_homologyTriangle]

/-- Remark 13.12.4 (2): the successive upper truncations of `K` and the degree-`a+1` cohomology
object of `K` form a distinguished triangle. -/
@[stacks 08J5]
theorem truncLE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncLE_step_homologyTriangle K a ∈ distTriang (DerivedCategory 𝒜) := by
  -- Proof comment: transport distinguishedness along the explicit triangle isomorphism.
  exact
    isomorphic_distinguished _
      (t.triangleLTLTGELT_distinguished (a + 1) (a + 2) (by omega) K) _
      (truncLE_step_homologyTriangleIso K a)

-- Proof sketch: the owner step triangle is `t.triangleLTGE (a+1)` applied to `\tau_{\ge a}K`;
-- the bridge data are the canonical homology isomorphism for the concentrated first term and the
-- canonical identification of the third term with `\tau_{\ge a+1}K`.
/-- Remark 13.12.4 (3): the degree-`a` cohomology piece extracted from the successive lower
truncations carries the same cohomology as `K` in degree `a`. -/
@[stacks 08J5]
noncomputable def truncGE_step_homologyIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅ (H a).obj K := by
  let eι :
      (H a).obj ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
        (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _
      ((H a).map ((t.truncLTι (a + 1)).app ((t.truncGE a).obj K)))
      (isIso_homologyMap_truncLTι (𝒜 := 𝒜) ((t.truncGE a).obj K) a (a + 1) (by omega))
  let eπ : (H a).obj K ≅ (H a).obj ((t.truncGE a).obj K) :=
    @asIso _ _ _ _
      ((H a).map ((t.truncGEπ a).app K))
      (isIso_homologyMap_truncGEπ (𝒜 := 𝒜) K a)
  -- Proof comment: compare first with the `τ_{\ge a}` piece and then with the original object.
  exact eι ≪≫ eπ.symm

/-- Remark 13.12.4 (3): the concentrated degree-`a` truncation piece is canonically the single
object on `H^a(K^\bullet)`. -/
@[stacks 08J5]
noncomputable def truncGE_step_termIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) ≅
      (singleFunctor 𝒜 a).obj ((H a).obj K) := by
  have hLE : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE a := by
    simpa using
      (inferInstance : ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)).IsLE ((a + 1) - 1))
  letI := hLE
  -- Proof comment: this one-step lower truncation piece is concentrated in degree `a`, so the
  -- concentrated comparison converts it to the single object on `H^a(K)`.
  exact
    singleFunctorIsoOfIsGEOfIsLE
      ((t.truncLT (a + 1)).obj ((t.truncGE a).obj K)) a ≪≫
      (singleFunctor 𝒜 a).mapIso (truncGE_step_homologyIso K a)

/-- Remark 13.12.4 (3), bridge/view form: the successive lower truncations of `K` fit into the
distinguished triangle whose first object is the cohomology term `H^a(K^\bullet)[-a]`. -/
@[stacks 08J5]
noncomputable def truncGE_step_homologyTriangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    Triangle (DerivedCategory 𝒜) :=
  Triangle.mk
    ((truncGE_step_termIso K a).inv ≫ (t.truncLTι (a + 1)).app ((t.truncGE a).obj K))
    ((t.natTransTruncGEOfLE a (a + 1) (le_add_of_nonneg_right zero_le_one)).app K)
    (((t.truncGE (a + 1)).map ((t.truncGEπ a).app K)) ≫
      (t.truncGEδLT (a + 1)).app ((t.truncGE a).obj K) ≫ ((truncGE_step_termIso K a).hom)⟦1⟧')

/-- Helper for Remark 13.12.4: the source-facing lower-step triangle is isomorphic to the owner
truncation triangle. -/
private noncomputable def truncGE_step_homologyTriangleIso
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncGE_step_homologyTriangle K a ≅
      (t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K) := by
  let f : (t.truncGE (a + 1)).obj K ⟶
      (t.truncGE (a + 1)).obj ((t.truncGE a).obj K) :=
    (t.truncGE (a + 1)).map ((t.truncGEπ a).app K)
  letI : IsIso f :=
    t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) K
  let e₃ : (t.truncGE (a + 1)).obj K ≅ (t.truncGE (a + 1)).obj ((t.truncGE a).obj K) :=
    asIso f
  let e :
      truncGE_step_homologyTriangle K a ≅
        (t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K) := by
    -- Proof comment: rewrite the owner triangle by replacing the first and third vertices with
    -- the canonical homology term and comparison isomorphism.
    refine Triangle.isoMk _ _ (truncGE_step_termIso K a).symm (Iso.refl _) e₃ ?_ ?_ ?_
    · simp [truncGE_step_homologyTriangle]
    · haveI : ((t.triangleLTGE (a + 1)).obj ((t.truncGE a).obj K)).obj₃.IsGE a := by
        dsimp
        exact t.isGE_of_ge _ a (a + 1) (by omega)
      exact t.from_truncGE_obj_ext (by
        simpa [truncGE_step_homologyTriangle, e₃, Category.assoc,
          t.π_natTransTruncGEOfLE_app] using
          (NatTrans.naturality (t.truncGEπ (a + 1)) ((t.truncGEπ a).app K)).symm)
    · simp [truncGE_step_homologyTriangle, e₃, f, Category.assoc]
  exact e

/-- Remark 13.12.4 (3): the degree-`a` cohomology object of `K` and the successive lower
truncations of `K` form a distinguished triangle. -/
@[stacks 08J5]
theorem truncGE_step_homology_triangle
    (K : DerivedCategory 𝒜) (a : ℤ) :
    truncGE_step_homologyTriangle K a ∈ distTriang (DerivedCategory 𝒜) := by
  -- Proof comment: this is the owner lower-step triangle after rewriting the first and third
  -- terms by the canonical isomorphisms constructed above.
  exact
    isomorphic_distinguished _
      (t.triangleLTGE_distinguished (a + 1) ((t.truncGE a).obj K)) _
      (truncGE_step_homologyTriangleIso K a)

end
