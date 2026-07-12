import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.3.1:
- primary domain: abelian sheaves on a Grothendieck site, together with the owner local
  injective/surjective criteria for sheaf morphisms and the kernel/cokernel comparison maps for
  sheafification and forgetting to presheaves;
- sampled owner API:
  `PreservesKernel.iso`,
  `PreservesCokernel.iso`,
  `Sheaf.isLocallyInjective_iff_injective`,
  `Sheaf.isLocallySurjective_iff_epi'`;
- best owner abstraction: the abelian sheaf category `Sheaf J AddCommGrpCat.{max u v}` together
  with the forgetful functor `sheafToPresheaf J AddCommGrpCat.{max u v}` and the sheafification
  functor `presheafToSheaf J AddCommGrpCat.{max u v}`;
- source/core/bridge triage:
  `source-facing`: the sectionwise injectivity criterion, the sectionwise local exactness criterion,
  and the cokernel/sheafification comparison;
  `core/canonical`: the preserved-kernel comparison and the owner local
  injective/surjective criteria for sheaf morphisms;
  `bridge/view`: the reformulation from objects of `Cᵒᵖ` to objects of `C` via `op`.

Primitive data are only a morphism of abelian sheaves or a short complex of abelian sheaves. The
kernel and local surjectivity owners already live upstream, so this file should not keep parallel
public aliases for them. The source-facing bridge statements belong under the owner namespaces
`Sheaf` and `ShortComplex`, and the genuinely new cokernel comparison belongs under `Sheaf`.
-/

/- Lemma 18.3.1 (1): the category of abelian sheaves on a site is an abelian category. -/
#check (inferInstance : Abelian (Sheaf J AddCommGrpCat.{max u v}))

/- Lemma 18.3.1 (2): the underlying abelian presheaf of the kernel sheaf of `φ` is the kernel of
the underlying morphism of abelian presheaves. This is exactly the preserved-kernel comparison
`PreservesKernel.iso` for `sheafToPresheaf J AddCommGrpCat.{max u v}`. -/
#check PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{max u v})

namespace Sheaf

variable {F G : Sheaf J AddCommGrpCat.{max u v}} (φ : F ⟶ G)

/-- Lemma 18.3.1 (3): a morphism of abelian sheaves is injective in the abelian-category sense if
and only if it is injective on every section of the underlying abelian presheaf. -/
-- Proof sketch: monomorphisms in the sheaf category are detected by the fully faithful inclusion
-- into presheaves, and monomorphisms in `AddCommGrpCat` are exactly injective group homomorphisms.
theorem mono_iff_app_injective :
    Mono φ ↔
      ∀ U : C, Function.Injective (φ.hom.app (op U)) := by
  constructor
  · intro hφ U
    letI : Mono φ := hφ
    have hφhom : Mono φ.hom := (sheafToPresheaf J AddCommGrpCat.{max u v}).map_mono φ
    exact (AddCommGrpCat.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app φ.hom).1 hφhom (op U))
  · intro hφ
    have hφhom : Mono φ.hom :=
      (NatTrans.mono_iff_mono_app φ.hom).2 fun U ↦
        (AddCommGrpCat.mono_iff_injective _).2 (hφ U.unop)
    exact (sheafToPresheaf J AddCommGrpCat.{max u v}).mono_of_mono_map hφhom

/-- Lemma 18.3.1 (4): injectivity on every section is equivalent to local injectivity as a
morphism of sheaves. -/
-- Proof sketch: rewrite `Sheaf.IsLocallyInjective φ` using the standard equivalence with
-- componentwise injectivity, then pass between objects of `Cᵒᵖ` and objects of `C`.
theorem isLocallyInjective_iff_app_injective :
    Sheaf.IsLocallyInjective φ ↔
      ∀ U : C, Function.Injective (φ.hom.app (op U)) := by
  constructor
  · intro hφ U
    exact (Sheaf.isLocallyInjective_iff_injective φ).1 hφ (op U)
  · intro hφ
    exact (Sheaf.isLocallyInjective_iff_injective φ).2 fun U ↦ hφ U.unop

/-- Lemma 18.3.1 (5): the cokernel sheaf of `φ` is the sheafification of the cokernel of the
underlying abelian presheaf morphism. -/
@[stacks 03CN]
noncomputable def cokernelSheafificationIso :
    cokernel φ ≅
      (presheafToSheaf J AddCommGrpCat.{max u v}).obj
        (cokernel ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ)) :=
  (cokernel.mapIso φ
      ((presheafToSheaf J AddCommGrpCat.{max u v}).map
        ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ))
      (sheafificationIso F)
      (sheafificationIso G)
      (by
        simpa using
          (sheafificationNatIso J AddCommGrpCat.{max u v}).hom.naturality φ)) ≪≫
    (PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{max u v})
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ)).symm

end Sheaf

/- Lemma 18.3.1 (6): a morphism of abelian sheaves is surjective in the abelian-category sense if
and only if it is locally surjective as a morphism of sheaves. This is the canonical owner theorem
`Sheaf.isLocallySurjective_iff_epi'`, specialized to abelian sheaves. -/
recall Sheaf.isLocallySurjective_iff_epi'

namespace ShortComplex

/-- Helper for Lemma 18.3.1: a section of the kernel sheaf over `U` is the same data as a
section of `S.X₂` over `U` that is annihilated by `S.g`. -/
noncomputable def kernel_section_equiv
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (U : C) :
    ((kernel S.g).obj.obj (Opposite.op U)) ≃
      {s : S.X₂.obj.obj (Opposite.op U) // S.g.hom.app (Opposite.op U) s = 0} :=
  { toFun := fun y ↦ by
      -- Route correction: expose the underlying section by the kernel inclusion itself, and only
      -- use `PreservesKernel.iso` when reconstructing a kernel section from a vanishing section.
      refine ⟨(kernel.ι S.g).hom.app (Opposite.op U) y, ?_⟩
      -- The kernel condition says the displayed section is annihilated by `S.g`.
      exact
        congrArg
            (fun k : kernel S.g ⟶ S.X₃ => k.hom.app (Opposite.op U) y)
            (kernel.condition S.g) |>.trans <| by simp
    invFun := fun s ↦
      ((PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{max u v}) S.g).inv.app
        (Opposite.op U))
        ((PreservesKernel.iso ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U)) S.g.hom).inv
          ((AddCommGrpCat.kernelIsoKer (S.g.hom.app (Opposite.op U))).inv s))
    left_inv := fun y ↦ by
      -- Compare after applying the monomorphism `kernel.ι S.g`; the concrete kernel comparison
      -- then collapses to the underlying section in `S.X₂(U)`.
      apply (AddCommGrpCat.mono_iff_injective ((kernel.ι S.g).hom.app (Opposite.op U))).1
        inferInstance
      let s :
          { s : S.X₂.obj.obj (Opposite.op U) // S.g.hom.app (Opposite.op U) s = 0 } :=
        ⟨(kernel.ι S.g).hom.app (Opposite.op U) y, by
          exact
            congrArg
                (fun k : kernel S.g ⟶ S.X₃ => k.hom.app (Opposite.op U) y)
                (kernel.condition S.g) |>.trans <| by simp⟩
      let z :
          ↑(kernel (S.g.hom.app (Opposite.op U))) :=
        (AddCommGrpCat.kernelIsoKer (S.g.hom.app (Opposite.op U))).inv s
      change
        ((kernel.ι S.g).hom.app (Opposite.op U))
            (((PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{max u v}) S.g).inv.app
              (Opposite.op U))
              ((PreservesKernel.iso ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U))
                S.g.hom).inv z)) =
          ((kernel.ι S.g).hom.app (Opposite.op U)) y
      have h₁ :=
        ConcreteCategory.congr_hom
          (NatTrans.congr_app
            (PreservesKernel.iso_inv_ι (sheafToPresheaf J AddCommGrpCat.{max u v}) S.g)
            (Opposite.op U))
          ((PreservesKernel.iso ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U)) S.g.hom).inv z)
      have h₂ :=
        ConcreteCategory.congr_hom
          (PreservesKernel.iso_inv_ι ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U))
            S.g.hom)
          z
      have h₃ :=
        ConcreteCategory.congr_hom
          (AddCommGrpCat.kernelIsoKer_inv_comp_ι (S.g.hom.app (Opposite.op U)))
          s
      exact h₁.trans (h₂.trans h₃)
    right_inv := fun s ↦ by
      -- The underlying section of the reconstructed kernel section is exactly the original `s`.
      ext
      let z :
          ↑(kernel (S.g.hom.app (Opposite.op U))) :=
        (AddCommGrpCat.kernelIsoKer (S.g.hom.app (Opposite.op U))).inv s
      change
        ((kernel.ι S.g).hom.app (Opposite.op U))
            (((PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{max u v}) S.g).inv.app
              (Opposite.op U))
              ((PreservesKernel.iso ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U))
                S.g.hom).inv z)) = s.1
      have h₁ :=
        ConcreteCategory.congr_hom
          (NatTrans.congr_app
            (PreservesKernel.iso_inv_ι (sheafToPresheaf J AddCommGrpCat.{max u v}) S.g)
            (Opposite.op U))
          ((PreservesKernel.iso ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U)) S.g.hom).inv z)
      have h₂ :=
        ConcreteCategory.congr_hom
          (PreservesKernel.iso_inv_ι ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op U))
            S.g.hom)
          z
      have h₃ :=
        ConcreteCategory.congr_hom
          (AddCommGrpCat.kernelIsoKer_inv_comp_ι (S.g.hom.app (Opposite.op U))) s
      exact h₁.trans (h₂.trans h₃) }

/-- Helper for Lemma 18.3.1: under `kernel_section_equiv`, restricting a kernel section along
`i : V ⟶ U` corresponds to restricting its underlying section of `S.X₂`. -/
lemma kernel_section_equiv_map
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    {U V : C} (i : V ⟶ U) (y : (kernel S.g).obj.obj (Opposite.op U)) :
    (kernel_section_equiv (J := J) S V (((kernel S.g).obj.map i.op) y)).1 =
      S.X₂.obj.map i.op ((kernel_section_equiv (J := J) S U y).1) := by
  -- Both sides are the same after unfolding `kernel_section_equiv`: this is exactly the
  -- naturality square of the kernel inclusion `kernel.ι S.g`.
  change
    ((kernel.ι S.g).hom.app (Opposite.op V)) (((kernel S.g).obj.map i.op) y) =
      S.X₂.obj.map i.op (((kernel.ι S.g).hom.app (Opposite.op U)) y)
  exact
    congrArg
      (fun f : (kernel S.g).obj.obj (Opposite.op U) ⟶ S.X₂.obj.obj (Opposite.op V) => f y)
      ((kernel.ι S.g).hom.naturality i.op)

/-- Helper for Lemma 18.3.1: membership in the image sieve of `kernel.lift` along `i : V ⟶ U`
is exactly the existence of a local section of `S.X₁` mapping to the restricted kernel section. -/
lemma kernel_lift_imageSieve_mem_iff
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    {U V : C} (i : V ⟶ U) (y : (kernel S.g).obj.obj (Opposite.op U)) :
    (Presheaf.imageSieve ((kernel.lift S.g S.f S.zero).hom) y).arrows i ↔
      ∃ t : S.X₁.obj.obj (Opposite.op V),
        S.f.hom.app (Opposite.op V) t =
          (kernel_section_equiv (J := J) S V (((kernel S.g).obj.map i.op) y)).1 := by
  -- Unfold image-sieve membership to an explicit local preimage equation in the kernel sheaf.
  rw [Presheaf.imageSieve_apply]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    -- Apply the kernel inclusion to transport equality back to the middle term `S.X₂`.
    have hι :
        ((kernel.ι S.g).hom.app (Opposite.op V))
            (((kernel.lift S.g S.f S.zero).hom.app (Opposite.op V)) t) =
          ((kernel.ι S.g).hom.app (Opposite.op V)) (((kernel S.g).obj.map i.op) y) :=
      congrArg ((kernel.ι S.g).hom.app (Opposite.op V)) ht
    have hcomp :
        ((kernel.ι S.g).hom.app (Opposite.op V))
            (((kernel.lift S.g S.f S.zero).hom.app (Opposite.op V)) t) =
          S.f.hom.app (Opposite.op V) t := by
      -- This is the defining factorization identity `kernel.lift ≫ kernel.ι = S.f` on sections.
      change
        (((kernel.lift S.g S.f S.zero ≫ kernel.ι S.g).hom.app (Opposite.op V)) t) =
          S.f.hom.app (Opposite.op V) t
      simpa using
        congrArg
          (fun k : S.X₁ ⟶ S.X₂ => k.hom.app (Opposite.op V) t)
          (kernel.lift_ι S.g S.f S.zero)
    -- The first component of `kernel_section_equiv` is exactly the kernel inclusion on sections.
    change
      S.f.hom.app (Opposite.op V) t =
        ((kernel.ι S.g).hom.app (Opposite.op V)) (((kernel S.g).obj.map i.op) y)
    exact hcomp.symm.trans hι
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    -- Equality in the kernel object is detected after applying the monomorphism `kernel.ι S.g`.
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι S.g).hom.app (Opposite.op V))).1
      inferInstance
    have hcomp :
        ((kernel.ι S.g).hom.app (Opposite.op V))
            (((kernel.lift S.g S.f S.zero).hom.app (Opposite.op V)) t) =
          S.f.hom.app (Opposite.op V) t := by
      -- Again use the defining identity of `kernel.lift`.
      change
        (((kernel.lift S.g S.f S.zero ≫ kernel.ι S.g).hom.app (Opposite.op V)) t) =
          S.f.hom.app (Opposite.op V) t
      simpa using
        congrArg
          (fun k : S.X₁ ⟶ S.X₂ => k.hom.app (Opposite.op V) t)
          (kernel.lift_ι S.g S.f S.zero)
    change
      ((kernel.ι S.g).hom.app (Opposite.op V))
          (((kernel.lift S.g S.f S.zero).hom.app (Opposite.op V)) t) =
        ((kernel.ι S.g).hom.app (Opposite.op V)) (((kernel S.g).obj.map i.op) y)
    change
      S.f.hom.app (Opposite.op V) t =
        ((kernel.ι S.g).hom.app (Opposite.op V)) (((kernel S.g).obj.map i.op) y) at ht
    exact hcomp.trans ht

/-- Helper for Lemma 18.3.1: local surjectivity of `kernel.lift` produces the covering-lift
criterion for sections of `S.X₂` killed by `S.g`. -/
lemma cover_lifts_of_isLocallySurjective_kernel_lift
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (hS : Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero)) :
    ∀ (U : C) (s : S.X₂.obj.obj (Opposite.op U)),
      S.g.hom.app (Opposite.op U) s = 0 →
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ t : S.X₁.obj.obj (Opposite.op I.Y),
            S.f.hom.app (Opposite.op I.Y) t = S.X₂.obj.map I.f.op s := by
  -- Route correction: use the image sieve of the kernel section corresponding to `s`.
  change Presheaf.IsLocallySurjective J (kernel.lift S.g S.f S.zero).hom at hS
  letI : Presheaf.IsLocallySurjective J (kernel.lift S.g S.f S.zero).hom := hS
  intro U s hs
  let y : (kernel S.g).obj.obj (Opposite.op U) :=
    (kernel_section_equiv (J := J) S U).symm ⟨s, hs⟩
  have hy : (kernel_section_equiv (J := J) S U y).1 = s := by
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (kernel_section_equiv (J := J) S U) ⟨s, hs⟩)
  let T : J.Cover U :=
    ⟨Presheaf.imageSieve ((kernel.lift S.g S.f S.zero).hom) y,
      Presheaf.imageSieve_mem J ((kernel.lift S.g S.f S.zero).hom) y⟩
  refine ⟨T, ?_⟩
  intro I
  -- Each arrow of the image sieve carries an explicit local lift in the source sheaf.
  obtain ⟨t, ht⟩ :=
    (kernel_lift_imageSieve_mem_iff (J := J) S I.f y).1 I.hf
  refine ⟨t, ?_⟩
  calc
    S.f.hom.app (Opposite.op I.Y) t =
        (kernel_section_equiv (J := J) S I.Y (((kernel S.g).obj.map I.f.op) y)).1 := ht
    _ = S.X₂.obj.map I.f.op ((kernel_section_equiv (J := J) S U y).1) :=
        kernel_section_equiv_map (J := J) S I.f y
    _ = S.X₂.obj.map I.f.op s := by rw [hy]

/-- Helper for Lemma 18.3.1: the sectionwise covering-lift criterion implies local surjectivity
of the canonical map `S.X₁ ⟶ kernel S.g`. -/
lemma isLocallySurjective_kernel_lift_of_cover_lifts
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (hS :
      ∀ (U : C) (s : S.X₂.obj.obj (Opposite.op U)),
        S.g.hom.app (Opposite.op U) s = 0 →
          ∃ T : J.Cover U, ∀ I : T.Arrow,
            ∃ t : S.X₁.obj.obj (Opposite.op I.Y),
              S.f.hom.app (Opposite.op I.Y) t = S.X₂.obj.map I.f.op s) :
    Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero) := by
  -- Move to the presheaf formulation, where local surjectivity is image-sieve covering.
  change Presheaf.IsLocallySurjective J (kernel.lift S.g S.f S.zero).hom
  constructor
  intro U y
  obtain ⟨T, hT⟩ := hS U (kernel_section_equiv (J := J) S U y).1
    (kernel_section_equiv (J := J) S U y).2
  -- The supplied cover refines the image sieve by turning each local lift into image membership.
  refine J.superset_covering ?_ T.condition
  intro V g hg
  let I : T.Arrow := ⟨V, g, hg⟩
  obtain ⟨t, ht⟩ := hT I
  exact
    (kernel_lift_imageSieve_mem_iff (J := J) S g y).2 <|
      ⟨t, by
        calc
          S.f.hom.app (Opposite.op V) t =
              S.X₂.obj.map g.op ((kernel_section_equiv (J := J) S U y).1) := ht
          _ = (kernel_section_equiv (J := J) S V (((kernel S.g).obj.map g.op) y)).1 := by
              simpa using (kernel_section_equiv_map (J := J) S g y).symm⟩

/-- Helper for Lemma 18.3.1: local surjectivity of the canonical map `S.X₁ ⟶ kernel S.g` is
equivalent to the sectionwise local lifting criterion from the textbook statement. -/
theorem isLocallySurjective_kernel_lift_iff_cover_lifts
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero) ↔
      ∀ (U : C) (s : S.X₂.obj.obj (Opposite.op U)),
        S.g.hom.app (Opposite.op U) s = 0 →
          ∃ T : J.Cover U, ∀ I : T.Arrow,
            ∃ t : S.X₁.obj.obj (Opposite.op I.Y),
              S.f.hom.app (Opposite.op I.Y) t = S.X₂.obj.map I.f.op s := by
  -- Assemble the source-text criterion from the two image-sieve directions proved above.
  constructor
  · intro hS
    exact cover_lifts_of_isLocallySurjective_kernel_lift (J := J) S hS
  · intro hS
    exact isLocallySurjective_kernel_lift_of_cover_lifts (J := J) S hS

/-- Lemma 18.3.1 (7): a short complex of abelian sheaves is exact at the middle term exactly when
every section killed by the right map becomes locally a section in the image of the left map. -/
-- Proof sketch: exactness in an abelian category is equivalent to the canonical map to the kernel
-- being epi; then translate epi to local surjectivity in the sheaf category and unpack the image
-- sieve condition objectwise over coverings.
theorem exact_iff_locally_surjective_sections
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    let F₁ := S.X₁.obj
    let F₂ := S.X₂.obj
    let f := S.f.hom
    let g := S.g.hom
    S.Exact ↔
      ∀ (U : C) (s : F₂.obj (Opposite.op U)), g.app (Opposite.op U) s = 0 →
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ t : F₁.obj (Opposite.op I.Y),
            f.app (Opposite.op I.Y) t = F₂.map I.f.op s := by
  -- Rewrite exactness to the epimorphicity of `kernel.lift`, then to local surjectivity.
  dsimp
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v}
    (kernel.lift S.g S.f S.zero)]
  exact isLocallySurjective_kernel_lift_iff_cover_lifts (J := J) S

end ShortComplex

end CategoryTheory
