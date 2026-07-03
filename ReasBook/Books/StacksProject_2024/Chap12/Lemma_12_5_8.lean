import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open Opposite

universe v u

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 12.5.8:
- primary domain: exactness detection in abelian categories via preadditive Yoneda/coyoneda and
  pointwise exactness in functor categories;
- sampled owner declarations:
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `NatTrans.mono_iff_mono_app`,
  `ShortComplex.exact_and_mono_f_iff_f_is_kernel`;
- best owner abstraction: the public statements remain source-facing assertions about a short
  complex `S : ShortComplex A`, while the proof layer should use the canonical functor-category
  exactness and mono owners rather than a bespoke evaluation-to-kernel wrapper;
- primitive data: `S : ShortComplex A` and the Hom functors `preadditiveYoneda.obj N` and
  `preadditiveCoyoneda.obj (op N)`;
- derived API: the pointwise exactness/mono families and the reflected kernel witnesses obtained
  from them;
- source/core/bridge triage:
  `source-facing`: the two iff-theorems below;
  `core/canonical`: the sampled owner declarations above;
  `bridge/view`: the functor-valued short complexes `S.op.map preadditiveCoyoneda` and
  `S.map preadditiveYoneda`. -/

private theorem evaluation_jointlyReflectsIsomorphisms
    (J : Type*) [Category J] (C : Type*) [Category C] :
    JointlyReflectIsomorphisms ((evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
  refine ⟨fun {X Y} f _ ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using (inferInstance : IsIso (((evaluation J C).obj j).map f))

/-- Lemma 12.5.8 (1): in an abelian category, a complex `M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is exact iff for every
object `N`, the induced sequence `0 ⟶ Hom(M₃, N) ⟶ Hom(M₂, N) ⟶ Hom(M₁, N)` is exact in abelian
groups. -/
-- Proof sketch: rewrite the source condition as `S.op.Exact ∧ Mono S.op.f`, then apply the
-- canonical left-exactness criterion for `preadditiveYoneda.obj N` and reflect back through the
-- Yoneda formalism.
theorem epi_exact_iff_hom_into_exact
    (S : ShortComplex A) :
    (S.Exact ∧ Epi S.g) ↔
      ∀ N : A,
        let T := S.op.map (preadditiveYoneda.obj N)
        T.Exact ∧ Mono T.f := by
  constructor
  · rintro ⟨hS, hg⟩ N
    have hmap := ((Functor.preservesFiniteLimits_tfae (preadditiveYoneda.obj N)).out 3 1).1
      (show PreservesFiniteLimits (preadditiveYoneda.obj N) from inferInstance)
    simpa using hmap S.op ⟨hS.op, by simpa using hg⟩
  · intro h
    let T : ShortComplex (A ⥤ AddCommGrpCat.{v}) := S.op.map preadditiveCoyoneda
    let c : KernelFork S.op.g := KernelFork.ofι S.op.f S.op.zero
    have hT_exact : T.Exact := by
      exact ((evaluation_jointlyReflectsIsomorphisms A AddCommGrpCat.{v}).exact_iff T).2
        fun N ↦ by simpa [T] using (h N).1
    have hT_mono : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      intro N
      simpa [T] using (h N).2
    have hc : IsLimit c := by
      refine isLimitOfReflects preadditiveCoyoneda ?_
      simpa [T, c] using
        (KernelFork.isLimitMapConeEquiv c preadditiveCoyoneda).symm
          ((T.exact_and_mono_f_iff_f_is_kernel).1 ⟨hT_exact, hT_mono⟩).some
    have hSop : S.op.Exact ∧ Mono S.op.f :=
      (S.op.exact_and_mono_f_iff_f_is_kernel).2 ⟨hc⟩
    exact ⟨(S.exact_op_iff).1 hSop.1, by simpa using hSop.2⟩

/-- Lemma 12.5.8 (2): in an abelian category, a complex `0 ⟶ M₁ ⟶ M₂ ⟶ M₃` is exact iff for every
object `N`, the induced sequence `0 ⟶ Hom(N, M₁) ⟶ Hom(N, M₂) ⟶ Hom(N, M₃)` is exact in abelian
groups. -/
-- Proof sketch: apply the canonical left-exactness criterion to `preadditiveCoyoneda.obj (op N)`,
-- then jointly reflect kernels through the functor-valued Yoneda embedding `preadditiveYoneda`.
theorem mono_exact_iff_hom_from_exact
    (S : ShortComplex A) :
    (S.Exact ∧ Mono S.f) ↔
      ∀ N : A,
        let T := S.map (preadditiveCoyoneda.obj (op N))
        T.Exact ∧ Mono T.f := by
  constructor
  · rintro ⟨hS, hf⟩ N
    have hmap := ((Functor.preservesFiniteLimits_tfae (preadditiveCoyoneda.obj (op N))).out 3 1).1
      (show PreservesFiniteLimits (preadditiveCoyoneda.obj (op N)) from inferInstance)
    simpa using hmap S ⟨hS, hf⟩
  · intro h
    let T : ShortComplex (Aᵒᵖ ⥤ AddCommGrpCat.{v}) := S.map preadditiveYoneda
    let c : KernelFork S.g := KernelFork.ofι S.f S.zero
    have hT_exact : T.Exact := by
      exact ((evaluation_jointlyReflectsIsomorphisms Aᵒᵖ AddCommGrpCat.{v}).exact_iff T).2
        fun N ↦ by simpa [T] using (h N.unop).1
    have hT_mono : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      intro N
      simpa [T] using (h N.unop).2
    have hc : IsLimit c := by
      refine isLimitOfReflects preadditiveYoneda ?_
      simpa [T, c] using
        (KernelFork.isLimitMapConeEquiv c preadditiveYoneda).symm
          ((T.exact_and_mono_f_iff_f_is_kernel).1 ⟨hT_exact, hT_mono⟩).some
    exact (S.exact_and_mono_f_iff_f_is_kernel).2 ⟨hc⟩

end
