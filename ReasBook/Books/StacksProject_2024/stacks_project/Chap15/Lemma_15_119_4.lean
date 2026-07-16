import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_119_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps in a submodule tower:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `determinantTensorIsoOfShortExact_spec`,
  * `Submodule.quotientQuotientEquivQuotient`;
- best owner abstraction:
  `core/canonical`: `determinantTensorIsoOfShortExact_spec` gives the wedge characterization for
    the comparison map of each short exact row used in the tower;
  `source-facing`: the main theorem specializes those comparison maps to the tower `K ≤ L ≤ M`
    and the quotients `L / K`, `M / L`, `M / K`;
  `bridge/view`: the quotient row `L / K → M / K → M / L` is expressed through the canonical
    submodule `L.map K.mkQ ⊆ M / K` and the standard quotient identifications.
- primitive data: the submodules `K ≤ L ≤ M` together with the finite projective hypotheses on
  `K`, `L / K`, and `M / L`;
- derived API: finiteness/projectivity of `L`, `M`, and `M / K`, and the resulting determinant
  comparison square.
-/

section SubmoduleTower

variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem projective_of_submodule_quotient (N : Submodule R M)
    [Module.Projective R N] [Module.Projective R (M ⧸ N)] :
    Module.Projective R M := by
  let s : (M ⧸ N) →ₗ[R] M :=
    Classical.choose
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  have hs : N.mkQ.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  obtain ⟨e, -, -⟩ :=
    ((Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ N) Subtype.val_injective
      N.mkQ_surjective).out 0 2 rfl rfl).mp ⟨s, hs⟩
  exact Module.Projective.of_equiv e.symm

private theorem exact_inclusion_mkQ (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (Submodule.inclusion hKL) (K.submoduleOf L).mkQ := by
  have hExact : Function.Exact (K.submoduleOf L).subtype (K.submoduleOf L).mkQ :=
    LinearMap.exact_subtype_mkQ (K.submoduleOf L)
  simpa [Submodule.inclusion] using
    (Function.Surjective.comp_exact_iff_exact
      (Submodule.submoduleOfEquivOfLe hKL).symm.surjective).2 hExact

namespace SubmoduleTower

private theorem finite_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] :
    Module.Finite R (K.submoduleOf L) :=
  Module.Finite.equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem projective_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] :
    Module.Projective R (K.submoduleOf L) :=
  Module.Projective.of_equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem finite_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥L := by
  letI := finite_submoduleOf K L hKL
  exact Module.Finite.of_submodule_quotient (K.submoduleOf L)

private theorem projective_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R ↥L := by
  letI := projective_submoduleOf K L hKL
  exact projective_of_submodule_quotient (K.submoduleOf L)

private theorem finite_M (L : Submodule R M)
    [Module.Finite R ↥L] [Module.Finite R (M ⧸ L)] :
    Module.Finite R M := by
  exact Module.Finite.of_submodule_quotient L

private theorem projective_M (L : Submodule R M)
    [Module.Projective R ↥L] [Module.Projective R (M ⧸ L)] :
    Module.Projective R M := by
  exact projective_of_submodule_quotient L

-- Bridge/view: the quotient of `L` by the induced submodule from `K` is canonically equivalent
-- to the image of `L` in `M ⧸ K`.
private noncomputable def quotientSubmoduleOfEquivImage (K L : Submodule R M) :
    (L ⧸ K.submoduleOf L) ≃ₗ[R] L.map K.mkQ :=
  let f : L →ₗ[R] M ⧸ K := K.mkQ.comp L.subtype
  let hk : f.ker = K.submoduleOf L := by
    ext x
    simp [f, Submodule.submoduleOf]
  let hr : f.range = L.map K.mkQ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

private theorem projective_quotientSubmodule (K L : Submodule R M)
    [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R (L.map K.mkQ) :=
  Module.Projective.of_equiv (quotientSubmoduleOfEquivImage K L)

private theorem finite_quotientSubmodule (K L : Submodule R M)
    [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥(L.map K.mkQ) :=
  Module.Finite.equiv (quotientSubmoduleOfEquivImage K L)

private theorem projective_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R (M ⧸ L)] :
    Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Projective.of_equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R (M ⧸ L)] :
    Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientKM (K : Submodule R M)
    [Module.Finite R M] :
    Module.Finite R (M ⧸ K) := by
  exact Module.Finite.quotient R K

private theorem projective_quotientKM (K L : Submodule R M)
    [Module.Projective R ↥(L.map K.mkQ)]
    [Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ)] :
    Module.Projective R (M ⧸ K) := by
  exact projective_of_submodule_quotient (L.map K.mkQ)

end SubmoduleTower

variable (K L : Submodule R M) (hKL : K ≤ L)
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R (L ⧸ K.submoduleOf L)] [Module.Projective R (L ⧸ K.submoduleOf L)]
variable [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)]

local notation3:max "det(" M ")" => Module.det R M

open SubmoduleTower

namespace SubmoduleTower

/-- The determinant comparison map for
`0 → K → L → L / K → 0`. -/
noncomputable def submoduleDeterminantIso :
    (det(↥K) ⊗[R] det(L ⧸ K.submoduleOf L)) ≃ₗ[R] det(↥L) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  determinantTensorIsoOfShortExact
    (Submodule.inclusion hKL)
    (K.submoduleOf L).mkQ
    (Submodule.inclusion_injective hKL)
    (K.submoduleOf L).mkQ_surjective
    (exact_inclusion_mkQ K L hKL)

/-- The determinant comparison map for
`0 → L → M → M / L → 0`. -/
noncomputable def ambientDeterminantIso :
    (det(↥L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  determinantTensorIsoOfShortExact
    L.subtype
    L.mkQ
    Subtype.val_injective
    L.mkQ_surjective
    (LinearMap.exact_subtype_mkQ L)

/-- The determinant comparison map for
`0 → K → M → M / K → 0`. -/
noncomputable def totalDeterminantIso :
    (det(↥K) ⊗[R] det(M ⧸ K)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  determinantTensorIsoOfShortExact
    K.subtype
    K.mkQ
    Subtype.val_injective
    K.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K)

/-- Bridge/view: the determinant comparison map for
`0 → L / K → M / K → M / L → 0`, obtained from the canonical exact row
`0 → L.map K.mkQ → M / K → (M / K) / L.map K.mkQ → 0`
through the standard quotient identifications. -/
noncomputable def quotientDeterminantIso :
    (det(L ⧸ K.submoduleOf L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M ⧸ K) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  (TensorProduct.congr
      (determinantLineMap (quotientSubmoduleOfEquivImage K L))
      (determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm)).trans
    (determinantTensorIsoOfShortExact
      (L.map K.mkQ).subtype
      (L.map K.mkQ).mkQ
      Subtype.val_injective
      (L.map K.mkQ).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (L.map K.mkQ)))

/-- Helper for Lemma 15.119.4: the quotient row map `L / K → M / K` is the inclusion of the
image `L.map K.mkQ ⊆ M / K` transported across the standard equivalence
`L / K ≃ L.map K.mkQ`. -/
private noncomputable def quotientRowInclusion :
    (L ⧸ K.submoduleOf L) →ₗ[R] M ⧸ K :=
  (L.map K.mkQ).subtype.comp (quotientSubmoduleOfEquivImage K L).toLinearMap

/-- Helper for Lemma 15.119.4: the transported inclusion `L / K → M / K` agrees with the obvious
composite `L → M → M / K` after passing to the quotient by `K`. -/
private theorem quotient_row_inclusion_comp_mkQ :
    (quotientRowInclusion (K := K) (L := L)).comp (K.submoduleOf L).mkQ =
      K.mkQ.comp L.subtype := by
  -- Both linear maps are induced by the same map `L → M / K`.
  ext x
  rfl

/-- Helper for Lemma 15.119.4: the inverse quotient-quotient equivalence is induced by the
canonical map `M / K → (M / K) / L.map K.mkQ` on classes modulo `L`. -/
private theorem quotient_quotient_equiv_symm_comp_mkQ :
    ((Submodule.quotientQuotientEquivQuotient K L hKL).symm.toLinearMap).comp L.mkQ =
      (L.map K.mkQ).mkQ.comp K.mkQ := by
  -- The inverse map in the third isomorphism theorem is definitionally the quotient map induced
  -- by `K.mkQ`.
  ext x
  rfl

/-- Helper for Lemma 15.119.4: evaluating the canonical determinant comparison map on the quotient
row `0 → L.map K.mkQ → M / K → (M / K) / L.map K.mkQ → 0` sends the transported right factor to
the chosen lift `ExteriorAlgebra.map K.mkQ yC`. -/
private theorem quotient_determinant_iso_unfolded_spec
    (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L))
    (yC : ExteriorAlgebra R M)
    (hyC : ExteriorAlgebra.map L.mkQ yC = (xC : ExteriorAlgebra R (M ⧸ L))) :
    let _ : Module.Finite R ↥L := finite_L K L hKL
    let _ : Module.Finite R M := finite_M L
    let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
    let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
    let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
    let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
    let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
    let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
    (determinantTensorIsoOfShortExact
      (L.map K.mkQ).subtype
      (L.map K.mkQ).mkQ
      Subtype.val_injective
      (L.map K.mkQ).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (L.map K.mkQ))
      (determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ ⊗ₜ[R]
        determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC) :
        ExteriorAlgebra R (M ⧸ K)) =
      ExteriorAlgebra.map (L.map K.mkQ).subtype
          ((determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ :
            Module.det R ↥(L.map K.mkQ)) : ExteriorAlgebra R ↥(L.map K.mkQ)) *
        ExteriorAlgebra.map K.mkQ yC := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  have hyC' :
      ExteriorAlgebra.map (L.map K.mkQ).mkQ (ExteriorAlgebra.map K.mkQ yC) =
        ((determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC :
          Module.det R ((M ⧸ K) ⧸ L.map K.mkQ)) :
            ExteriorAlgebra R ((M ⧸ K) ⧸ L.map K.mkQ)) := by
    -- Proof comment: transport the chosen lift `yC` along the third-isomorphism equivalence so it
    -- becomes the right determinant factor for the quotient row.
    calc
      ExteriorAlgebra.map (L.map K.mkQ).mkQ (ExteriorAlgebra.map K.mkQ yC) =
          ExteriorAlgebra.map ((L.map K.mkQ).mkQ.comp K.mkQ) yC := by
            rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      _ =
          ExteriorAlgebra.map (((Submodule.quotientQuotientEquivQuotient K L hKL).symm.toLinearMap).comp L.mkQ) yC := by
            simpa using
              congrArg
                (fun φ : M →ₗ[R] ((M ⧸ K) ⧸ L.map K.mkQ) ↦ ExteriorAlgebra.map φ yC)
                (quotient_quotient_equiv_symm_comp_mkQ (K := K) (L := L) (hKL := hKL)).symm
      _ =
          ExteriorAlgebra.map ((Submodule.quotientQuotientEquivQuotient K L hKL).symm.toLinearMap)
            (ExteriorAlgebra.map L.mkQ yC) := by
            rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      _ =
          ((determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC :
            Module.det R ((M ⧸ K) ⧸ L.map K.mkQ)) :
              ExteriorAlgebra R ((M ⧸ K) ⧸ L.map K.mkQ)) := by
            rw [hyC, determinantLineMap_apply]
  -- Proof comment: now the canonical short-exact determinant formula applies directly to the
  -- quotient row `L.map K.mkQ → M / K → (M / K) / L.map K.mkQ`.
  simpa using
    (determinantTensorIsoOfShortExact_spec
      (R := R)
      (f := (L.map K.mkQ).subtype)
      (g := (L.map K.mkQ).mkQ)
      (hf := Subtype.val_injective)
      (hg := (L.map K.mkQ).mkQ_surjective)
      (hexact := LinearMap.exact_subtype_mkQ (L.map K.mkQ))
      (x' := determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ)
      (x'' := determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC)
      (y'' := ExteriorAlgebra.map K.mkQ yC)
      hyC')

/-- Helper for Lemma 15.119.4: the transported determinant factor on `L / K` rewrites back to the
obvious image of the chosen lift `yQ : ExteriorAlgebra R L` inside `M / K`. -/
private theorem image_determinant_factor_rewrite
    (xQ : det(L ⧸ K.submoduleOf L)) (yQ : ExteriorAlgebra R ↥L)
    (hyQ : ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ =
      (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L))) :
    ExteriorAlgebra.map (L.map K.mkQ).subtype
      (((determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ :
        Module.det R ↥(L.map K.mkQ)) : ExteriorAlgebra R ↥(L.map K.mkQ))) =
      ExteriorAlgebra.map K.mkQ (ExteriorAlgebra.map L.subtype yQ) := by
  -- Rewrite the determinant-line transport as the exterior-algebra map induced by the quotient-row
  -- inclusion `L / K → M / K`, then identify that inclusion with `K.mkQ ∘ L.subtype`.
  rw [determinantLineMap_apply]
  rw [← hyQ]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [show (L.map K.mkQ).subtype.comp (quotientSubmoduleOfEquivImage K L).toLinearMap =
      quotientRowInclusion (K := K) (L := L) by rfl]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [quotient_row_inclusion_comp_mkQ]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

/-- Helper for Lemma 15.119.4: `TensorProduct.congr` sends a pure tensor to the pure tensor of the
transported factors. -/
private theorem tensorproduct_congr_apply_tmul
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') (x : A) (y : B) :
    TensorProduct.congr e₁ e₂ (x ⊗ₜ[R] y) = e₁ x ⊗ₜ[R] e₂ y := by
  -- Proof comment: `TensorProduct.congr` is defined on pure tensors by applying each equivalence
  -- to its corresponding factor.
  rfl

/-- Helper for Lemma 15.119.4: the top-path `TensorProduct.congr` shell on a pure tensor is just
the literal pure tensor in `det(L) ⊗ det(M / L)`. -/
private theorem ambient_route_input_on_pure_tensor
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ((TensorProduct.congr
        (submoduleDeterminantIso K L hKL)
        (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
      (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      submoduleDeterminantIso K L hKL (xK ⊗ₜ[R] xQ) ⊗ₜ[R] xC := by
  -- Proof comment: peel off the top transport wrapper before applying any determinant-line wedge
  -- formula.
  simpa using
    (tensorproduct_congr_apply_tmul
      (e₁ := submoduleDeterminantIso K L hKL)
      (e₂ := LinearEquiv.refl R (det(M ⧸ L)))
      (x := xK ⊗ₜ[R] xQ)
      (y := xC))

/-- Helper for Lemma 15.119.4: the determinant comparison map for `0 → K → L → L / K → 0`
evaluated on a pure tensor is the expected wedge with a chosen lift in `ExteriorAlgebra R L`. -/
private theorem submodule_determinant_iso_on_pure_tensor
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (yQ : ExteriorAlgebra R ↥L)
    (hyQ : ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ =
      (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L))) :
    (submoduleDeterminantIso K L hKL (xK ⊗ₜ[R] xQ) : ExteriorAlgebra R ↥L) =
      ExteriorAlgebra.map (Submodule.inclusion hKL) (xK : ExteriorAlgebra R ↥K) * yQ := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  -- Proof comment: after specializing the short-exact wedge formula to
  -- `0 → K → L → L / K → 0`, the target is exactly the source-facing submodule determinant map.
  simpa [submoduleDeterminantIso] using
    (determinantTensorIsoOfShortExact_spec
      (R := R)
      (f := Submodule.inclusion hKL)
      (g := (K.submoduleOf L).mkQ)
      (hf := Submodule.inclusion_injective hKL)
      (hg := (K.submoduleOf L).mkQ_surjective)
      (hexact := exact_inclusion_mkQ K L hKL)
      (x' := xK)
      (x'' := xQ)
      (y'' := yQ)
      hyQ)

/-- Helper for Lemma 15.119.4: the bottom-path reassociation and quotient-row transport send a
pure tensor to the literal pure tensor in `det(K) ⊗ det(M / K)`. -/
private theorem total_route_input_on_pure_tensor
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    (((TensorProduct.assoc R
        (det(↥K))
        (det(L ⧸ K.submoduleOf L))
        (det(M ⧸ L))).trans
      (TensorProduct.congr
        (LinearEquiv.refl R (det(↥K)))
        (quotientDeterminantIso K L hKL))).toLinearMap
      (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      xK ⊗ₜ[R] quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC) := by
  -- Proof comment: first reassociate the tensor and then evaluate the quotient-row transport on
  -- the right pure tensor.
  simpa [LinearEquiv.trans_apply, TensorProduct.assoc_tmul] using
    (tensorproduct_congr_apply_tmul
      (e₁ := LinearEquiv.refl R (det(↥K)))
      (e₂ := quotientDeterminantIso K L hKL)
      (x := xK)
      (y := xQ ⊗ₜ[R] xC))

/-- Helper for Lemma 15.119.4: on a pure tensor, the quotient-row bridge
`quotientDeterminantIso K L hKL` is exactly the canonical quotient-row determinant comparison map
fed with the transported determinant factors. -/
private theorem quotient_determinant_iso_apply_tmul
    (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    let _ : Module.Finite R ↥L := finite_L K L hKL
    let _ : Module.Finite R M := finite_M L
    let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
    let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
    let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
    let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
    let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
    let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
    (quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC) : ExteriorAlgebra R (M ⧸ K)) =
      (determinantTensorIsoOfShortExact
        (L.map K.mkQ).subtype
        (L.map K.mkQ).mkQ
        Subtype.val_injective
        (L.map K.mkQ).mkQ_surjective
        (LinearMap.exact_subtype_mkQ (L.map K.mkQ))
        (determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ ⊗ₜ[R]
          determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC) :
          ExteriorAlgebra R (M ⧸ K)) := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  -- Proof comment: this removes the outer `TensorProduct.congr`/`.trans` shell from
  -- `quotientDeterminantIso` on a pure tensor so the canonical quotient-row wedge formula can be
  -- applied directly.
  rw [quotientDeterminantIso, LinearEquiv.trans_apply]
  -- Proof comment: after opening the composite equivalence, only the tensor-factor transport
  -- remains, and `TensorProduct.congr` evaluates definitionally on pure tensors.
  rw [tensorproduct_congr_apply_tmul]

/-- Helper for Lemma 15.119.4: the bridge `quotientDeterminantIso` sends a pure tensor to the
exterior product of chosen lifts in `ExteriorAlgebra R (M ⧸ K)`. -/
private theorem quotient_determinant_iso_on_pure_tensor
    (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L))
    (yQ : ExteriorAlgebra R ↥L) (yC : ExteriorAlgebra R M)
    (hyQ : ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ = (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L)))
    (hyC : ExteriorAlgebra.map L.mkQ yC = (xC : ExteriorAlgebra R (M ⧸ L))) :
    (quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC) : ExteriorAlgebra R (M ⧸ K)) =
      ExteriorAlgebra.map K.mkQ (ExteriorAlgebra.map L.subtype yQ * yC) := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  -- Route correction: the earlier proof tried to normalize the transported left and right
  -- determinant factors inside one large `simpa`. The stable route is to separate the canonical
  -- quotient-row computation from the rewrite of the transported `L / K` factor.
  calc
    (quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC) : ExteriorAlgebra R (M ⧸ K)) =
        (determinantTensorIsoOfShortExact
          (L.map K.mkQ).subtype
          (L.map K.mkQ).mkQ
          Subtype.val_injective
          (L.map K.mkQ).mkQ_surjective
          (LinearMap.exact_subtype_mkQ (L.map K.mkQ))
          (determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ ⊗ₜ[R]
            determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm xC) :
            ExteriorAlgebra R (M ⧸ K)) := by
          simpa using quotient_determinant_iso_apply_tmul (K := K) (L := L) (hKL := hKL) xQ xC
    _ =
        ExteriorAlgebra.map (L.map K.mkQ).subtype
            ((determinantLineMap (quotientSubmoduleOfEquivImage K L) xQ :
              Module.det R ↥(L.map K.mkQ)) : ExteriorAlgebra R ↥(L.map K.mkQ)) *
          ExteriorAlgebra.map K.mkQ yC := by
          simpa using
            quotient_determinant_iso_unfolded_spec
              (K := K) (L := L) (hKL := hKL) xQ xC yC hyC
    _ = ExteriorAlgebra.map K.mkQ (ExteriorAlgebra.map L.subtype yQ) *
          ExteriorAlgebra.map K.mkQ yC := by
          rw [image_determinant_factor_rewrite (K := K) (L := L) xQ yQ hyQ]
    _ = ExteriorAlgebra.map K.mkQ (ExteriorAlgebra.map L.subtype yQ * yC) := by
          rw [← map_mul]

/-- Helper for Lemma 15.119.4: determinant elements on `L / K` and `M / L` admit simultaneous
lifts to the corresponding exterior algebras on `L` and `M`. -/
private theorem exists_exterior_lifts_of_tower_quotients
    (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ∃ yQ : ExteriorAlgebra R ↥L, ∃ yC : ExteriorAlgebra R M,
      ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ =
        (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L)) ∧
      ExteriorAlgebra.map L.mkQ yC = (xC : ExteriorAlgebra R (M ⧸ L)) := by
  have hQ : Function.Surjective (ExteriorAlgebra.map (K.submoduleOf L).mkQ) :=
    (ExteriorAlgebra.map_surjective_iff).2 (K.submoduleOf L).mkQ_surjective
  have hC : Function.Surjective (ExteriorAlgebra.map L.mkQ) :=
    (ExteriorAlgebra.map_surjective_iff).2 L.mkQ_surjective
  -- Proof comment: both quotient maps are surjective, so the induced exterior-algebra maps are
  -- surjective as well and we may choose preimages of the two determinant factors independently.
  obtain ⟨yQ, hyQ⟩ := hQ (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L))
  obtain ⟨yC, hyC⟩ := hC (xC : ExteriorAlgebra R (M ⧸ L))
  exact ⟨yQ, yC, hyQ, hyC⟩

/-- Helper for Lemma 15.119.4: after choosing quotient lifts, the top route around the determinant
tower square is the common wedge expression in `ExteriorAlgebra R M`. -/
private theorem ambient_route_on_pure_tensor_with_lifts
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L))
    (yQ : ExteriorAlgebra R ↥L) (yC : ExteriorAlgebra R M)
    (hyQ : ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ =
      (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L)))
    (hyC : ExteriorAlgebra.map L.mkQ yC = (xC : ExteriorAlgebra R (M ⧸ L))) :
    (ambientDeterminantIso K L hKL
      ((TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) :
        ExteriorAlgebra R M) =
      ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        (ExteriorAlgebra.map L.subtype yQ * yC) := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  have hcomp : L.subtype.comp (Submodule.inclusion hKL) = K.subtype := by
    -- Proof comment: both composites send an element of `K` to the same element of `M`.
    ext x
    rfl
  -- Route correction: normalize the top tensor input first, then apply one wedge formula for the
  -- ambient row and reuse the already isolated wedge formula for the submodule row.
  calc
    (ambientDeterminantIso K L hKL
      ((TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) :
        ExteriorAlgebra R M) =
      (ambientDeterminantIso K L hKL
        (submoduleDeterminantIso K L hKL (xK ⊗ₜ[R] xQ) ⊗ₜ[R] xC) :
          ExteriorAlgebra R M) := by
        rw [ambient_route_input_on_pure_tensor (K := K) (L := L) (hKL := hKL) xK xQ xC]
    _ =
      ExteriorAlgebra.map L.subtype
          ((submoduleDeterminantIso K L hKL (xK ⊗ₜ[R] xQ) :
            Module.det R ↥L) : ExteriorAlgebra R ↥L) * yC := by
        -- Proof comment: this is the wedge formula for `0 → L → M → M / L → 0`.
        simpa [ambientDeterminantIso] using
          (determinantTensorIsoOfShortExact_spec
            (R := R)
            (f := L.subtype)
            (g := L.mkQ)
            (hf := Subtype.val_injective)
            (hg := L.mkQ_surjective)
            (hexact := LinearMap.exact_subtype_mkQ L)
            (x' := submoduleDeterminantIso K L hKL (xK ⊗ₜ[R] xQ))
            (x'' := xC)
            (y'' := yC)
            hyC)
    _ =
      ExteriorAlgebra.map L.subtype
          (ExteriorAlgebra.map (Submodule.inclusion hKL) (xK : ExteriorAlgebra R ↥K) * yQ) * yC := by
        rw [submodule_determinant_iso_on_pure_tensor
          (K := K) (L := L) (hKL := hKL) xK xQ yQ hyQ]
    _ =
      (ExteriorAlgebra.map L.subtype
          (ExteriorAlgebra.map (Submodule.inclusion hKL) (xK : ExteriorAlgebra R ↥K)) *
        ExteriorAlgebra.map L.subtype yQ) * yC := by
        rw [map_mul]
    _ =
      (ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        ExteriorAlgebra.map L.subtype yQ) * yC := by
        -- Proof comment: collapse the transported inclusion `K → L → M` back to `K → M`.
        rw [show ExteriorAlgebra.map L.subtype
            (ExteriorAlgebra.map (Submodule.inclusion hKL) (xK : ExteriorAlgebra R ↥K)) =
              ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) by
              rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hcomp]]
    _ =
      ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        (ExteriorAlgebra.map L.subtype yQ * yC) := by
        rw [mul_assoc]

/-- Helper for Lemma 15.119.4: after choosing quotient lifts, the bottom route around the
determinant tower square is the same common wedge expression in `ExteriorAlgebra R M`. -/
private theorem total_route_on_pure_tensor_with_lifts
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L))
    (yQ : ExteriorAlgebra R ↥L) (yC : ExteriorAlgebra R M)
    (hyQ : ExteriorAlgebra.map (K.submoduleOf L).mkQ yQ =
      (xQ : ExteriorAlgebra R (L ⧸ K.submoduleOf L)))
    (hyC : ExteriorAlgebra.map L.mkQ yC = (xC : ExteriorAlgebra R (M ⧸ L))) :
    (totalDeterminantIso K L hKL
      (((TensorProduct.assoc R
          (det(↥K))
          (det(L ⧸ K.submoduleOf L))
          (det(M ⧸ L))).trans
        (TensorProduct.congr
          (LinearEquiv.refl R (det(↥K)))
          (quotientDeterminantIso K L hKL))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) :
        ExteriorAlgebra R M) =
      ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        (ExteriorAlgebra.map L.subtype yQ * yC) := by
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  -- Route correction: normalize the reassociation shell first, then feed the already normalized
  -- quotient-row factor into the total short exact row `0 → K → M → M / K → 0`.
  calc
    (totalDeterminantIso K L hKL
      (((TensorProduct.assoc R
          (det(↥K))
          (det(L ⧸ K.submoduleOf L))
          (det(M ⧸ L))).trans
        (TensorProduct.congr
          (LinearEquiv.refl R (det(↥K)))
          (quotientDeterminantIso K L hKL))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) :
        ExteriorAlgebra R M) =
      (totalDeterminantIso K L hKL
        (xK ⊗ₜ[R] quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC)) :
          ExteriorAlgebra R M) := by
        rw [total_route_input_on_pure_tensor (K := K) (L := L) (hKL := hKL) xK xQ xC]
    _ =
      ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        (ExteriorAlgebra.map L.subtype yQ * yC) := by
        -- Proof comment: the chosen total-row lift is exactly
        -- `ExteriorAlgebra.map L.subtype yQ * yC`, whose image in `M / K` is the quotient-row
        -- determinant factor computed above.
        simpa [totalDeterminantIso] using
          (determinantTensorIsoOfShortExact_spec
            (R := R)
            (f := K.subtype)
            (g := K.mkQ)
            (hf := Subtype.val_injective)
            (hg := K.mkQ_surjective)
            (hexact := LinearMap.exact_subtype_mkQ K)
            (x' := xK)
            (x'' := quotientDeterminantIso K L hKL (xQ ⊗ₜ[R] xC))
            (y'' := ExteriorAlgebra.map L.subtype yQ * yC)
            ((quotient_determinant_iso_on_pure_tensor
              (K := K) (L := L) (hKL := hKL) xQ xC yQ yC hyQ hyC).symm))

/-- Helper for Lemma 15.119.4: on a pure tensor with chosen lifts through `L → L / K` and
`M → M / L`, both routes around the determinant square evaluate to the same exterior-algebra
expression in `ExteriorAlgebra R M`. -/
private theorem determinant_tensor_iso_tower_on_pure_tensor
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ((ambientDeterminantIso K L hKL
        ((TensorProduct.congr
            (submoduleDeterminantIso K L hKL)
            (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) : Module.det R M) : ExteriorAlgebra R M) =
      ((totalDeterminantIso K L hKL
          (((TensorProduct.assoc R
              (det(↥K))
              (det(L ⧸ K.submoduleOf L))
              (det(M ⧸ L))).trans
            (TensorProduct.congr
              (LinearEquiv.refl R (det(↥K)))
              (quotientDeterminantIso K L hKL))).toLinearMap
            (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) : Module.det R M) : ExteriorAlgebra R M) := by
  obtain ⟨yQ, yC, hyQ, hyC⟩ :=
    exists_exterior_lifts_of_tower_quotients (K := K) (L := L) xQ xC
  -- Proof comment: both paths evaluate to the same wedge expression once the quotient factors are
  -- represented by lifts in `ExteriorAlgebra R L` and `ExteriorAlgebra R M`.
  calc
    ambientDeterminantIso K L hKL
        ((TensorProduct.congr
            (submoduleDeterminantIso K L hKL)
            (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      ExteriorAlgebra.map K.subtype (xK : ExteriorAlgebra R ↥K) *
        (ExteriorAlgebra.map L.subtype yQ * yC) := by
        exact ambient_route_on_pure_tensor_with_lifts
          (K := K) (L := L) (hKL := hKL) xK xQ xC yQ yC hyQ hyC
    _ =
      totalDeterminantIso K L hKL
        (((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) := by
        symm
        exact total_route_on_pure_tensor_with_lifts
          (K := K) (L := L) (hKL := hKL) xK xQ xC yQ yC hyQ hyC

-- Proof sketch: derive the finite projective structures on `L`, `M`, and `M / K` from the three
-- source-facing hypotheses using split exactness for the quotient rows. Then compare the two ways
-- of passing from `det K ⊗ det(L / K) ⊗ det(M / L)` to `det M` by evaluating both composites on
-- pure tensors, rewriting the left quotient bridge through the canonical identifications
-- `L / K ≃ L.map K.mkQ` and `(M / K) / (L / K) ≃ M / L`, and applying the wedge characterization
-- from Lemma `15.119.2` to each short exact row.
/-- Lemma 15.119.4: for submodules `K ≤ L` of an `R`-module `M`, if `K`, `L / K`, and `M / L` are
finite projective, then the determinant comparison maps from Lemma `15.119.2` for the short exact
sequences
`0 → K → L → L / K → 0`, `0 → L → M → M / L → 0`, `0 → K → M → M / K → 0`, and
`0 → L / K → M / K → M / L → 0`
form a commutative square. The left vertical map is the source-facing quotient-row bridge
`quotientDeterminantIso K L hKL`, built from the canonical identifications
`L / K ≃ L.map K.mkQ` and `(M / K) / (L / K) ≃ M / L`. -/
theorem determinant_tensor_iso_tower_commutes :
    CommSq
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap)
      (ModuleCat.ofHom <|
        ((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap)
      (ModuleCat.ofHom <|
        (ambientDeterminantIso K L hKL).toLinearMap)
      (ModuleCat.ofHom <| (totalDeterminantIso K L hKL).toLinearMap) := by
  -- TODO: extend `determinant_tensor_iso_tower_on_pure_tensor` from pure tensors to the full
  -- triple tensor product by a two-stage `TensorProduct.induction_on`. The remaining blocker is
  -- elaboration/`whnf` timeout in the additive branches when normalizing the two transported
  -- composite linear maps, not a missing wedge identity.
  sorry

/-- The determinant square from `determinant_tensor_iso_tower_commutes`, evaluated on a pure
tensor. -/
theorem determinant_tensor_iso_tower_commutes_apply
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ambientDeterminantIso K L hKL
      ((TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      totalDeterminantIso K L hKL
        (((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) := by
  -- Evaluate the commutative square from `determinant_tensor_iso_tower_commutes` on the chosen
  -- pure tensor.
  simpa using
    LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (determinant_tensor_iso_tower_commutes (K := K) (L := L) hKL).w)
      (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)

end SubmoduleTower
end SubmoduleTower
