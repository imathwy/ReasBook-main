import StacksProject_2024.stacks_project.Chap19.Remark_19_9_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (A)

/- Domain-style sampling for Lemma 19.9.1:
- primary domain: Grothendieck pretopologies on abelian categories, with coverings given by single
  epimorphisms;
- sampled owner declarations:
  `Pretopology`,
  `ExactStructure.singletonAdmissibleEpiPretopology`,
  `ExactStructure.mem_singletonAdmissibleEpiPretopology_iff`,
  `Abelian.epi_pullback_of_epi_f`;
- best owner abstraction: the chapter owner `ExactStructure.singletonAdmissibleEpiPretopology`,
  specialized to the canonical exact structure on an abelian category;
- primitive data: the exact structure whose admissible short complexes are the short exact ones;
- derived API: the singleton-epimorphism pretopology and its membership characterization.

Source/core/bridge triage:
- `source-facing`: `singletonEpiPretopology`;
- `core/canonical`: `ExactStructure.singletonAdmissibleEpiPretopology`;
- `bridge/view`: the canonical exact structure on an abelian category and the identification of its
  admissible epimorphisms with ordinary epimorphisms.

Primitive-versus-derived check:
- the singleton-epimorphism site should not duplicate the pretopology constructor from
  `ExactStructure`;
- the abelian exact structure is the only primitive bridge data added here;
- the singleton-cover site and its cover-membership criterion are derived from that owner. -/

/-- Helper for Lemma 19.9.1: a short exact complex in an abelian category is a kernel-cokernel
pair. -/
theorem shortExact_isKernelCokernelPair {S : ShortComplex A} (hS : S.ShortExact) :
    IsKernelCokernelPair S := by
  constructor
  · -- Short exactness identifies the left map as the kernel of the right map.
    exact ⟨ShortComplex.ShortExact.fIsKernel hS⟩
  · -- Short exactness also identifies the right map as the cokernel of the left map.
    exact ⟨ShortComplex.ShortExact.gIsCokernel hS⟩

/-- Helper for Lemma 19.9.1: for the short-exact admissibility class, admissible monomorphisms are
exactly monomorphisms. -/
theorem isAdmissibleMono_shortExact_iff {X Y : A} (i : X ⟶ Y) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i ↔ Mono i := by
  constructor
  · rintro ⟨Z, p, w, hS⟩
    -- The witness short exact sequence records that `i` is the mono left map.
    simpa using hS.mono_f
  · intro hi
    -- The canonical cokernel sequence gives the required short exact witness.
    exact ⟨cokernel i, cokernel.π i, cokernel.condition i,
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) hi inferInstance⟩

/-- Helper for Lemma 19.9.1: for the short-exact admissibility class, admissible epimorphisms are
exactly epimorphisms. -/
theorem isAdmissibleEpi_shortExact_iff {Y Z : A} (p : Y ⟶ Z) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p ↔ Epi p := by
  constructor
  · rintro ⟨X, i, w, hS⟩
    -- The witness short exact sequence records that `p` is the epi right map.
    simpa using hS.epi_g
  · intro hp
    -- The canonical kernel sequence gives the required short exact witness.
    exact ⟨kernel p, kernel.ι p, kernel.condition p,
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp⟩

/-- Helper for Lemma 19.9.1: short exactness is stable under isomorphism of short complexes. -/
theorem abelianExactStructure_ofIso {S T : ShortComplex A} (e : S ≅ T) :
    ({S' : ShortComplex A | S'.ShortExact} : Set (ShortComplex A)) S →
      ({S' : ShortComplex A | S'.ShortExact} : Set (ShortComplex A)) T := by
  intro hS
  -- Transport short exactness across the given isomorphism.
  exact ShortComplex.shortExact_of_iso e hS

/-- Helper for Lemma 19.9.1: identities are admissible monomorphisms for the short-exact exact
structure. -/
theorem abelianExactStructure_id_admissibleMono (X : A) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) (𝟙 X) := by
  -- Rewrite admissibility into the ordinary mono condition for identities.
  exact (isAdmissibleMono_shortExact_iff (A := A) (𝟙 X)).2 inferInstance

/-- Helper for Lemma 19.9.1: identities are admissible epimorphisms for the short-exact exact
structure. -/
theorem abelianExactStructure_id_admissibleEpi (X : A) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) (𝟙 X) := by
  -- Rewrite admissibility into the ordinary epi condition for identities.
  exact (isAdmissibleEpi_shortExact_iff (A := A) (𝟙 X)).2 inferInstance

/-- Helper for Lemma 19.9.1: admissible monomorphisms for the short-exact exact structure are
stable under composition. -/
theorem abelianExactStructure_comp_admissibleMono {X Y Z : A} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i)
    (hj : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) j) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) (i ≫ j) := by
  -- Reduce to the ordinary fact that monos compose.
  refine (isAdmissibleMono_shortExact_iff (A := A) (i ≫ j)).2 ?_
  let _ : Mono i := (isAdmissibleMono_shortExact_iff (A := A) i).1 hi
  let _ : Mono j := (isAdmissibleMono_shortExact_iff (A := A) j).1 hj
  infer_instance

/-- Helper for Lemma 19.9.1: admissible epimorphisms for the short-exact exact structure are
stable under composition. -/
theorem abelianExactStructure_comp_admissibleEpi {X Y Z : A} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p)
    (hq : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) q) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) (p ≫ q) := by
  -- Reduce to the ordinary fact that epis compose.
  refine (isAdmissibleEpi_shortExact_iff (A := A) (p ≫ q)).2 ?_
  let _ : Epi p := (isAdmissibleEpi_shortExact_iff (A := A) p).1 hp
  let _ : Epi q := (isAdmissibleEpi_shortExact_iff (A := A) q).1 hq
  infer_instance

/-- Helper for Lemma 19.9.1: pushouts of admissible monomorphisms are admissible monomorphisms in
the short-exact exact structure. -/
theorem abelianExactStructure_pushout_admissibleMono {X Y X' : A} (i : X ⟶ Y) (f : X ⟶ X')
    (hi : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i) :
    ∃ (_ : HasPushout i f), IsAdmissibleMono ({S : ShortComplex A | S.ShortExact})
      (pushout.inr i f) := by
  -- Pushouts exist in an abelian category, and pushouts preserve monos.
  let _ : HasPushout i f := inferInstance
  refine ⟨inferInstance, (isAdmissibleMono_shortExact_iff (A := A) (pushout.inr i f)).2 ?_⟩
  let _ : Mono i := (isAdmissibleMono_shortExact_iff (A := A) i).1 hi
  infer_instance

/-- Helper for Lemma 19.9.1: pullbacks of admissible epimorphisms are admissible epimorphisms in
the short-exact exact structure. -/
theorem abelianExactStructure_pullback_admissibleEpi {Y Z Z' : A} (p : Y ⟶ Z) (f : Z' ⟶ Z)
    (hp : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p) :
    ∃ (_ : HasPullback p f), IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact})
      (pullback.snd p f) := by
  -- Pullbacks exist in an abelian category, and pullbacks preserve epis.
  let _ : HasPullback p f := inferInstance
  refine ⟨inferInstance, (isAdmissibleEpi_shortExact_iff (A := A) (pullback.snd p f)).2 ?_⟩
  let _ : Epi p := (isAdmissibleEpi_shortExact_iff (A := A) p).1 hp
  infer_instance

/-- The canonical exact structure on an abelian category, whose admissible short complexes are the
short exact ones. -/
def abelianExactStructure : ExactStructure A where
  admissible := {S | S.ShortExact}
  isKernelCokernelPair := shortExact_isKernelCokernelPair (A := A)
  ofIso := abelianExactStructure_ofIso (A := A)
  id_admissibleMono := abelianExactStructure_id_admissibleMono (A := A)
  id_admissibleEpi := abelianExactStructure_id_admissibleEpi (A := A)
  comp_admissibleMono := abelianExactStructure_comp_admissibleMono (A := A)
  comp_admissibleEpi := abelianExactStructure_comp_admissibleEpi (A := A)
  pushout_admissibleMono := abelianExactStructure_pushout_admissibleMono (A := A)
  pullback_admissibleEpi := abelianExactStructure_pullback_admissibleEpi (A := A)

/-- In the canonical exact structure on an abelian category, the admissible epimorphisms are
exactly the epimorphisms. -/
theorem abelianExactStructure_admissibleEpi_iff {Y Z : A} (p : Y ⟶ Z) :
    (abelianExactStructure A).AdmissibleEpi p ↔ Epi p := by
  -- Unfold the exact-structure predicate and rewrite it through the short-exact bridge.
  exact isAdmissibleEpi_shortExact_iff (A := A) p

/-- Lemma 19.9.1: the singleton presieves generated by epimorphisms define a pretopology on an
abelian category, i.e. the site whose coverings are single surjective morphisms. -/
abbrev singletonEpiPretopology : Pretopology A :=
  ExactStructure.singletonAdmissibleEpiPretopology (abelianExactStructure A)

variable {A}

/-- A cover in `singletonEpiPretopology` is exactly a singleton presieve generated by an
epimorphism. -/
theorem mem_singletonEpiPretopology_iff {X : A} {S : Presieve X} :
    S ∈ singletonEpiPretopology A X ↔
      ∃ (Y : A) (f : Y ⟶ X), Epi f ∧ S = Presieve.singleton f := by
  -- Rewrite the generic singleton-admissible-epi criterion using the abelian admissible-epi
  -- identification proved above.
  simpa [singletonEpiPretopology, abelianExactStructure_admissibleEpi_iff] using
    (ExactStructure.mem_singletonAdmissibleEpiPretopology_iff (E := abelianExactStructure A)
      (X := X) (S := S))

end CategoryTheory
