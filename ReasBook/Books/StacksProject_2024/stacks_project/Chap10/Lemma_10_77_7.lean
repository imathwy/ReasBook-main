import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_77_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open CategoryTheory.ShortComplex.ShortExact
open LinearMap

section

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- 
Domain triage:
- primary domain: projective modules over nilpotent thickenings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `exists_projective_lift_of_projective_quotient_of_isNilpotent`,
  `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_isNilpotent`;
- best owner abstraction: `Module.Projective R M`, with quotient comparisons handled through the
  canonical quotient-map API rather than a local wrapper;
- primitive data: the nilpotent two-sided ideal `I`, the module `M`, and projectivity of `M / IM`;
- derived API: a projective lift `P`, a comparison map `P → M`, and projectivity of `M`.

Layer classification:
- `source-facing`: the commutative flatness criterion in the second section;
- `core/canonical`: `Module.Projective`;
- `bridge/view`: the quotient-exact descent criterion below, used only as an internal reduction
  step from flatness to projectivity.
-/

private theorem quotientMapByIdeal_exact
    {N P Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (I : Ideal R) (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x :=
      Submodule.smul_induction_on hx'
        (fun r hr z _ ↦ by
          obtain ⟨y, rfl⟩ := hg z
          refine ⟨r • y, ?_, by simp⟩
          exact Submodule.smul_mem_smul hr (by simp))
        (fun y z hy hz ↦ by
          rcases hy with ⟨y', hy', rfl⟩
          rcases hz with ⟨z', hz', rfl⟩
          exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩)
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    rw [hn]
    simpa using hyI
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

-- Proof sketch: lift the projective quotient module across `I`, use projectivity of the lift to
-- produce a comparison map `P → M` that is an isomorphism modulo `I`, obtain surjectivity of that
-- map by nilpotent Nakayama, and use the assumed exactness of reduction modulo `I` on short exact
-- sequences ending in `M` to kill its kernel modulo `I`. A second nilpotent Nakayama argument then
-- forces the kernel to vanish. This is an internal bridge from flatness to the public source-facing
-- theorem in the commutative section below.
private theorem projective_of_projective_quotient_of_isNilpotent_of_quotientExact_aux
    (hI : IsNilpotent I)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hmodI :
      ∀ {N P : Type v} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
        (f : N →ₗ[R] P) (g : P →ₗ[R] M),
        Function.Injective f → Function.Surjective g → Function.Exact f g →
          Function.Injective (f.quotientMapByIdeal I)) :
    Module.Projective R M := by
  obtain ⟨P, _, _, e, hP⟩ :=
    exists_projective_lift_of_projective_quotient_of_isNilpotent hquot
  letI : Module.Projective R P := hP
  let gbar : P →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    (LinearEquiv.restrictScalars R e).toLinearMap.comp (I • (⊤ : Submodule R P)).mkQ
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ gbar
      (Submodule.mkQ_surjective _)
  have hsmul : I • (⊤ : Submodule R P) ≤ Submodule.comap g (I • (⊤ : Submodule R M)) :=
    Submodule.smul_top_le_comap_smul_top I g
  have hcomp :
      ((I • (⊤ : Submodule R P)).mapQ (I • (⊤ : Submodule R M)) g hsmul).comp
          (I • (⊤ : Submodule R P)).mkQ =
        (I • (⊤ : Submodule R M)).mkQ.comp g :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) g
  have hgquot : g.quotientMapByIdeal I = (LinearEquiv.restrictScalars R e).toLinearMap := by
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x
    simpa [LinearMap.quotientMapByIdeal, gbar] using
      DFunLike.congr_fun hcomp x |>.trans (DFunLike.congr_fun hg x)
  have hg_surj : Function.Surjective g := by
    apply surjective_of_quotientMap_surjective_of_isNilpotent I g
    · simpa [hgquot] using (LinearEquiv.restrictScalars R e).surjective
    · exact hI
  have hExact : Function.Exact (LinearMap.ker g).subtype g := by
    exact LinearMap.exact_subtype_ker_map g
  have hQuotExact :
      Function.Exact ((LinearMap.ker g).subtype.quotientMapByIdeal I) (g.quotientMapByIdeal I) :=
    quotientMapByIdeal_exact I (LinearMap.ker g).subtype g hExact hg_surj
  have hQuotSubtypeInj : Function.Injective ((LinearMap.ker g).subtype.quotientMapByIdeal I) :=
    hmodI (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype hg_surj hExact
  have hQuotInj : Function.Injective (g.quotientMapByIdeal I) := by
    simpa [hgquot] using (LinearEquiv.restrictScalars R e).injective
  have hRangeBot : LinearMap.range ((LinearMap.ker g).subtype.quotientMapByIdeal I) = ⊥ := by
    rw [← LinearMap.exact_iff.mp hQuotExact, LinearMap.ker_eq_bot]
    exact hQuotInj
  have hQuotSubtypeZero : (LinearMap.ker g).subtype.quotientMapByIdeal I = 0 :=
    LinearMap.range_eq_bot.mp hRangeBot
  have hKerQuotSubsingleton :
      Subsingleton ((LinearMap.ker g) ⧸ (I • (⊤ : Submodule R (LinearMap.ker g)))) := by
    refine ⟨fun x y ↦ hQuotSubtypeInj ?_⟩
    simp [hQuotSubtypeZero]
  have hIKer : I • (⊤ : Submodule R (LinearMap.ker g)) = ⊤ := by
    rwa [Submodule.Quotient.subsingleton_iff] at hKerQuotSubsingleton
  have hKerSubsingleton : Subsingleton (LinearMap.ker g) :=
    subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent I hIKer hI
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.subsingleton_iff_eq_bot.mp hKerSubsingleton
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective g ⟨hg_inj, hg_surj⟩)

end

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

private theorem quotientMapByIdeal_lTensor_naturality
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul N' I ∘ₗ f.lTensor (R ⧸ I) := by
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

private theorem injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

private theorem quotientMapByIdeal_injective_of_exact_of_flat
    {N P : Type v}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g) :
    Function.Injective (f.quotientMapByIdeal I) := by
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    simpa [lTensor_inj_iff_rTensor_inj] using
      lTensor_injective_of_exact_of_flat g hg f hf hExact (R ⧸ I)
  exact injective_of_ladder_linearEquiv (quotientMapByIdeal_lTensor_naturality f) hTensorInj

/-- Lemma 10.77.7: if `I` is a nilpotent ideal of a commutative ring `R`, `M / IM` is a
projective `R ⧸ I`-module, and `M` is flat over `R`, then `M` is projective over `R`. The owner
predicate is the canonical `Module.Projective R M`; the quotient-exact descent criterion used in
the proof is kept internal. -/
theorem projective_of_projective_quotient_of_isNilpotent_of_flat
    (hI : IsNilpotent I)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective R M := by
  refine projective_of_projective_quotient_of_isNilpotent_of_quotientExact_aux hI hquot ?_
  intro N _ _ P _ _ f g hf hg hExact
  exact quotientMapByIdeal_injective_of_exact_of_flat f g hf hg hExact

end
