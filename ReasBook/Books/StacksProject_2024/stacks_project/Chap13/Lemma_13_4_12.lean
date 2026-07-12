import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryTheory.Arrow
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling:
- primary domain: morphisms in a pretriangulated preadditive category, viewed up to isomorphism in
  the arrow category and compared with the canonical biproduct projection/inclusion model;
- relevant upstream owner declarations in this domain:
  `CategoryTheory.Arrow`,
  `Arrow.isoMk`,
  `CategoryTheory.IsIsomorphic`,
  `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel`,
  `biprod.isKernelSndKernelFork` / `biprod.isCokernelInlCokernelFork`;
- best owner abstraction: `Arrow D` is the canonical owner for saying that a morphism is
  isomorphic to another morphism, and `IsIsomorphic` is the canonical Prop-level owner for
  existence of such an isomorphism; the textbook decomposition should be expressed there rather
  than by primitive object isomorphisms plus a raw composite equality or a raw `Nonempty` wrapper;
- primitive data vs derived API: the primitive ingredients are `HasKernel f`, `HasCokernel f`,
  and the standard arrow `biprod.snd ≫ biprod.inl`; the explicit domain/codomain isomorphisms are
  derived data packaged by an arrow-category isomorphism, whose existence is then recorded by the
  Prop-level owner `IsIsomorphic`.

This file is therefore `source-facing`: it keeps the Stacks equivalence, but refines clause `(3)`
to the canonical arrow-category owner instead of a parallel low-level encoding.
-/

-- Proof sketch: for `(3) → (1), (2)`, transport kernels and cokernels along the displayed
-- isomorphisms and use the standard kernel of `biprod.snd` and cokernel of `biprod.inl`. For
-- `(1) → (3)`, a morphism with kernel is mono after restricting away the kernel summand, hence
-- split mono in a pretriangulated category; combine the kernel splitting and
-- `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` for the resulting cokernel decomposition. The
-- implication `(2) → (3)` is dual.
omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Helper for Lemma 13.4.12: an arrow isomorphism transports kernel existence backward. -/
private theorem hasKernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasKernel g] : HasKernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Transport the canonical kernel fork of `g` across the source and target isomorphisms.
  have hcomp : (kernel.ι g ≫ eX.inv) ≫ f = 0 := by
    calc
      (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
        simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
      _ = 0 := by simp
  let fork : KernelFork f := KernelFork.ofι (kernel.ι g ≫ eX.inv) hcomp
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_fork : (Iso.refl _).hom ≫ fork.ι = kernel.ι g ≫ eX.inv := by
    simp [fork]
  -- The universal property follows from the corresponding universal property for `g`.
  refine ⟨⟨fork, ?_⟩⟩
  exact IsKernel.ofIso g (kernelIsKernel g) fork eX.symm eY.symm (Iso.refl _) h_arrow h_fork

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Helper for Lemma 13.4.12: an arrow isomorphism transports cokernel existence backward. -/
private theorem hasCokernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasCokernel g] : HasCokernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Transport the canonical cokernel cofork of `g` across the arrow-category square.
  have hcomp : f ≫ (eY.hom ≫ cokernel.π g) = 0 := by
    calc
      f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
        simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
      _ = 0 := by simp
  let cofork : CokernelCofork f := CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) hcomp
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_cofork : eY.inv ≫ cofork.π = cokernel.π g ≫ (Iso.refl _).hom := by
    simp [cofork]
  -- The universal property again transports along the same square.
  refine ⟨⟨cofork, ?_⟩⟩
  exact IsCokernel.ofIso g (cokernelIsCokernel g) cofork eX.symm eY.symm (Iso.refl _) h_arrow
    h_cofork

/-- Helper for Lemma 13.4.12: the model map `biprod.snd ≫ biprod.inl` has the expected kernel and
cokernel. -/
private theorem projection_then_coprojection_hasKernel_hasCokernel (K Z Q : D) :
    HasKernel (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) ∧
      HasCokernel (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) := by
  constructor
  · let fork : KernelFork (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) :=
      KernelFork.ofι (biprod.inl : K ⟶ K ⊞ Z) (by simp)
    refine ⟨⟨fork, Fork.IsLimit.mk fork (fun s ↦ s.ι ≫ biprod.fst) ?_ ?_⟩⟩
    · intro s
      have hsnd : s.ι ≫ biprod.snd = 0 := by
        apply Mono.right_cancellation (f := (biprod.inl : Z ⟶ Z ⊞ Q))
        simpa [Category.assoc] using s.condition
      -- Once the `Z`-component vanishes, the map is determined by its `K`-component.
      apply biprod.hom_ext
      · simp [fork]
      · simpa [fork] using hsnd.symm
    · intro s m hm
      -- The kernel lift is unique because precomposing with `biprod.fst` recovers the map.
      calc
        m = m ≫ fork.ι ≫ biprod.fst := by simp [fork]
        _ = s.ι ≫ biprod.fst := by simpa [Category.assoc] using congrArg (fun k ↦ k ≫ biprod.fst) hm
  · let cofork : CokernelCofork (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) :=
      CokernelCofork.ofπ (biprod.snd : Z ⊞ Q ⟶ Q) (by simp)
    refine ⟨⟨cofork, Cofork.IsColimit.mk cofork (fun s ↦ biprod.inr ≫ s.π) ?_ ?_⟩⟩
    · intro s
      have hinl : biprod.inl ≫ s.π = 0 := by
        -- Cancel the split epimorphism `biprod.snd` from the cofork condition.
        have hcancel :
            (biprod.snd : K ⊞ Z ⟶ Z) ≫ (biprod.inl ≫ s.π) =
              (biprod.snd : K ⊞ Z ⟶ Z) ≫ 0 := by
          calc
            (biprod.snd : K ⊞ Z ⟶ Z) ≫ (biprod.inl ≫ s.π) =
                (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) ≫ s.π := by
                  rw [Category.assoc]
            _ = 0 ≫ s.π := Cofork.condition s
            _ = (biprod.snd : K ⊞ Z ⟶ Z) ≫ 0 := by simp
        exact Epi.left_cancellation (f := (biprod.snd : K ⊞ Z ⟶ Z)) (biprod.inl ≫ s.π) 0
          hcancel
      -- Once the `Z`-summand condition is enforced, only the `Q`-component remains.
      apply biprod.hom_ext'
      · simpa [cofork, hinl]
      · simp [cofork]
    · intro s m hm
      -- Uniqueness follows by postcomposing with the canonical coprojection `biprod.inr`.
      calc
        m = biprod.inr ≫ cofork.π ≫ m := by simp [cofork]
        _ = biprod.inr ≫ s.π := by rw [hm]

/-- Helper for Lemma 13.4.12: a monomorphism is identified with the canonical coprojection
`biprod.inl` by the source distinguished-triangle splitting route. -/
private theorem exists_iso_target_of_mono {X Y : D} (f : X ⟶ Y) [Mono f] :
    ∃ Z : D, ∃ e : Y ≅ X ⊞ Z, f ≫ e.hom = biprod.inl := by
  -- Extend `f` to a distinguished triangle and force the third morphism to vanish by monicity.
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ _ hT (inferInstance : Mono f)
  -- The split-triangle theorem identifies the middle object with the required biproduct.
  obtain ⟨e, hf, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT hzero
  exact ⟨Z, e, hf⟩

/-- Helper for Lemma 13.4.12: an epimorphism is identified with the canonical projection
`biprod.snd` by the dual distinguished-triangle splitting route. -/
private theorem exists_iso_source_of_epi {X Y : D} (f : X ⟶ Y) [Epi f] :
    ∃ K : D, ∃ e : X ≅ K ⊞ Y, e.hom ≫ biprod.snd = f := by
  -- Dually, extend `f` to a distinguished triangle and force the third morphism to vanish.
  obtain ⟨K, i, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi f)
  obtain ⟨e, _, hf⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i f h) hT hzero
  exact ⟨K, e, by simpa using hf.symm⟩

/-- Helper for Lemma 13.4.12: if `biprod.inl` is the kernel of `biprod.snd ≫ g`, then `g` is
monic. -/
private theorem mono_of_biprod_inl_is_kernel {K Z Y : D} (g : Z ⟶ Y)
    (hker : IsLimit
      (KernelFork.ofι (biprod.inl : K ⟶ K ⊞ Z) (by simp :
        biprod.inl ≫ (biprod.snd ≫ g) = 0))) : Mono g := by
  refine Mono.mk ?_
  intro W u v huv
  have hsub : (u - v) ≫ g = 0 := by
    simpa [CategoryTheory.Preadditive.sub_comp, huv]
  let liftData := KernelFork.IsLimit.lift' hker (biprod.lift 0 (u - v)) (by
    simpa [Category.assoc, hsub])
  have hlift : liftData.1 ≫ (biprod.inl : K ⟶ K ⊞ Z) = biprod.lift 0 (u - v) := liftData.2
  have hzero : u - v = 0 := by
    calc
      u - v = (biprod.lift 0 (u - v)) ≫ biprod.snd := by simp
      _ = (liftData.1 ≫ (biprod.inl : K ⟶ K ⊞ Z)) ≫ biprod.snd := by rw [hlift]
      _ = 0 := by simp [Category.assoc]
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 13.4.12: if `biprod.snd` is the cokernel of `g ≫ biprod.inl`, then `g` is
epic. -/
private theorem epi_of_biprod_snd_is_cokernel {X Z Q : D} (g : X ⟶ Z)
    (hcok : IsColimit
      (CokernelCofork.ofπ (biprod.snd : Z ⊞ Q ⟶ Q) (by simp [Category.assoc] :
        (g ≫ biprod.inl) ≫ biprod.snd = 0))) : Epi g := by
  refine Epi.mk ?_
  intro W u v huv
  have hsub : g ≫ (u - v) = 0 := by
    simpa [CategoryTheory.Preadditive.comp_sub, huv]
  let descData := CokernelCofork.IsColimit.desc' hcok (biprod.desc (u - v) 0) (by
    simpa [hsub])
  have hdesc : (biprod.snd : Z ⊞ Q ⟶ Q) ≫ descData.1 = biprod.desc (u - v) 0 := descData.2
  have hzero : u - v = 0 := by
    calc
      u - v = biprod.inl ≫ biprod.desc (u - v) 0 := by simp
      _ = biprod.inl ≫ ((biprod.snd : Z ⊞ Q ⟶ Q) ≫ descData.1) := by rw [hdesc]
      _ = 0 := by simp
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 13.4.12: if `f` has a kernel, then the source proof splits off the kernel
summand and reduces to a monomorphism. -/
private theorem isomorphic_to_projection_then_coprojection_of_hasKernel {X Y : D} (f : X ⟶ Y)
    [HasKernel f] :
    ∃ K Z Q : D,
      IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) := by
  -- Route correction: follow the source proof by splitting off the kernel first, then splitting
  -- the resulting monomorphism, rather than appealing to an abstract complement theorem.
  obtain ⟨Z, eX, hkι⟩ := exists_iso_target_of_mono (kernel.ι f)
  let g : Z ⟶ Y := biprod.inr ≫ eX.inv ≫ f
  have hkι' : biprod.inl ≫ eX.inv = kernel.ι f := by
    calc
      biprod.inl ≫ eX.inv = (kernel.ι f ≫ eX.hom) ≫ eX.inv := by rw [hkι]
      _ = kernel.ι f := by simp [Category.assoc]
  have hfactor : eX.inv ≫ f = biprod.snd ≫ g := by
    -- After identifying `X` with `kernel f ⊞ Z`, the map kills the kernel summand.
    apply biprod.hom_ext'
    · calc
        biprod.inl ≫ (eX.inv ≫ f) = (biprod.inl ≫ eX.inv) ≫ f := by simp
        _ = kernel.ι f ≫ f := by rw [hkι']
        _ = 0 := by simp
        _ = biprod.inl ≫ (biprod.snd ≫ g) := by simp
    · simp [g]
  let fork :
      KernelFork (biprod.snd ≫ g) := KernelFork.ofι (biprod.inl : kernel f ⟶ kernel f ⊞ Z) (by
        simp)
  have hker_transport : IsLimit fork := by
    -- Transport the kernel universal property of `f` directly to the rewritten map `biprod.snd ≫ g`.
    refine IsKernel.ofIso f (kernelIsKernel f) fork eX (Iso.refl _) (Iso.refl _) ?_ ?_
    · simpa [Category.assoc] using (congrArg (fun k ↦ eX.hom ≫ k) hfactor).symm
    · simpa [fork] using hkι.symm
  have hmonoG : Mono g := by
    -- The transported kernel description forces the reduced map to be monic.
    exact mono_of_biprod_inl_is_kernel g hker_transport
  obtain ⟨Q, eY, hg⟩ := exists_iso_target_of_mono g
  have h_arrow :
      eX.hom ≫ (biprod.snd ≫ biprod.inl : kernel f ⊞ Z ⟶ Z ⊞ Q) = f ≫ eY.hom := by
    -- Compose the kernel splitting with the mono splitting of the reduced map.
    calc
      eX.hom ≫ (biprod.snd ≫ biprod.inl : kernel f ⊞ Z ⟶ Z ⊞ Q) =
          eX.hom ≫ biprod.snd ≫ (g ≫ eY.hom) := by rw [hg]
      _ = (eX.hom ≫ biprod.snd ≫ g) ≫ eY.hom := by simp [Category.assoc]
      _ = f ≫ eY.hom := by
        simpa [Category.assoc] using (congrArg (fun k ↦ eX.hom ≫ k ≫ eY.hom) hfactor).symm
  exact ⟨kernel f, Z, Q, ⟨Arrow.isoMk eX eY h_arrow⟩⟩

/-- Helper for Lemma 13.4.12: if `f` has a cokernel, then the dual source proof splits off the
cokernel summand and reduces to an epimorphism. -/
private theorem isomorphic_to_projection_then_coprojection_of_hasCokernel {X Y : D} (f : X ⟶ Y)
    [HasCokernel f] :
    ∃ K Z Q : D,
      IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) := by
  -- Route correction: dualize the source proof by splitting off the cokernel first.
  obtain ⟨Z, eY, hπ⟩ := exists_iso_source_of_epi (cokernel.π f)
  let g : X ⟶ Z := f ≫ eY.hom ≫ biprod.fst
  have hfactor : f ≫ eY.hom = g ≫ biprod.inl := by
    -- After identifying `Y` with `Z ⊞ cokernel f`, the map lands in the first summand.
    apply biprod.hom_ext
    · simp [g, Category.assoc]
    · simpa [g, Category.assoc, hπ] using cokernel.condition f
  let cofork :
      CokernelCofork (g ≫ biprod.inl : X ⟶ Z ⊞ cokernel f) :=
        CokernelCofork.ofπ (biprod.snd : Z ⊞ cokernel f ⟶ cokernel f) (by simp [Category.assoc])
  have hcok_transport : IsColimit cofork := by
    -- Transport the cokernel universal property of `f` to the rewritten map `g ≫ biprod.inl`.
    refine IsCokernel.ofIso f (cokernelIsCokernel f) cofork (Iso.refl _) eY (Iso.refl _) ?_ ?_
    · simpa [Category.assoc] using hfactor.symm
    · simpa [cofork] using hπ
  have hepiG : Epi g := by
    -- The transported cokernel description forces the reduced map to be epic.
    apply epi_of_biprod_snd_is_cokernel
    simpa [cofork, Category.assoc] using hcok_transport
  obtain ⟨K, eX, hg⟩ := exists_iso_source_of_epi g
  have h_arrow :
      eX.hom ≫ (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ cokernel f) = f ≫ eY.hom := by
    -- Combine the epi splitting with the previous factorization through the first summand.
    calc
      eX.hom ≫ (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ cokernel f) =
          (eX.hom ≫ biprod.snd) ≫ biprod.inl := by simp [Category.assoc]
      _ = g ≫ biprod.inl := by rw [hg]
      _ = f ≫ eY.hom := hfactor.symm
  exact ⟨K, Z, cokernel f, ⟨Arrow.isoMk eX eY h_arrow⟩⟩

/-- Lemma 13.4.12: for a morphism `f : X ⟶ Y` in a pre-triangulated category, the following are
equivalent: `f` has a kernel, `f` has a cokernel, and `f` is isomorphic to a composition
`K ⊞ Z ⟶ Z ⟶ Z ⊞ Q` given by a projection followed by a coprojection. The isomorphism is
expressed in the canonical arrow category `Arrow D`, using the Prop-level owner
`IsIsomorphic`. -/
theorem tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection {X Y : D}
    (f : X ⟶ Y) :
    List.TFAE
      [ HasKernel f
      , HasCokernel f
      , ∃ K Z Q : D,
          IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) ] := by
  tfae_have 1 → 3 := by
    intro hf
    letI : HasKernel f := hf
    -- The source proof splits off the kernel summand and then the remaining mono summand.
    exact isomorphic_to_projection_then_coprojection_of_hasKernel f
  tfae_have 2 → 3 := by
    intro hf
    letI : HasCokernel f := hf
    -- The dual source proof splits off the cokernel summand and then the remaining epi summand.
    exact isomorphic_to_projection_then_coprojection_of_hasCokernel f
  tfae_have 3 → 1 := by
    rintro ⟨K, Z, Q, ⟨e⟩⟩
    have hmodel := projection_then_coprojection_hasKernel_hasCokernel K Z Q
    letI : HasKernel (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) := hmodel.1
    -- Transport the standard kernel of the model map back along the displayed arrow isomorphism.
    exact hasKernel_of_arrow_iso e
  tfae_have 3 → 2 := by
    rintro ⟨K, Z, Q, ⟨e⟩⟩
    have hmodel := projection_then_coprojection_hasKernel_hasCokernel K Z Q
    letI : HasCokernel (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) := hmodel.2
    -- Transport the standard cokernel of the model map back along the same arrow isomorphism.
    exact hasCokernel_of_arrow_iso e
  tfae_finish

/-- In a pre-triangulated category, a morphism has a kernel if and only if it has a cokernel. -/
theorem hasKernel_iff_hasCokernel_of_pretriangulated {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔ HasCokernel f :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 0 1

/-- In a pre-triangulated category, a morphism has a kernel if and only if it is isomorphic in the
arrow category to a projection followed by a coprojection. -/
theorem hasKernel_iff_isomorphicTo_projection_then_coprojection {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔
      ∃ K Z Q : D,
        IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 0 2

/-- In a pre-triangulated category, a morphism has a cokernel if and only if it is isomorphic in
the arrow category to a projection followed by a coprojection. -/
theorem hasCokernel_iff_isomorphicTo_projection_then_coprojection {X Y : D} (f : X ⟶ Y) :
    HasCokernel f ↔
      ∃ K Z Q : D,
        IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 1 2

end CategoryTheory
