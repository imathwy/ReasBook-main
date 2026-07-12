import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Definition 10.54.1 (1): a ring homomorphism `R → S` is essentially of finite type if it is the
canonical mathlib notion `RingHom.EssFiniteType`, equivalently if `S` is the localization of an
`R`-algebra of finite type. -/
recall RingHom.EssFiniteType

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.54.1 (2): an `R`-algebra `S` is essentially of finite presentation if it is the
localization of a finitely presented `R`-algebra. -/
class EssFinitePresentation : Prop where
  cond :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
      (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
      IsLocalization M S

/-- Unfolding `Algebra.EssFinitePresentation` gives the standard localization-of-a-finitely-
presented-`R`-algebra condition. -/
theorem essFinitePresentation_iff :
    EssFinitePresentation R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := by
  constructor
  · intro h
    exact h.cond
  · intro h
    exact ⟨h⟩

/-- A finitely presented `R`-algebra is essentially of finite presentation over `R`. -/
theorem EssFinitePresentation.of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S := by
  sorry

/-- A finitely presented `R`-algebra is essentially of finite presentation over `R`. -/
instance of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S :=
  EssFinitePresentation.of_finitePresentation R S

/-- A localization of a finitely presented `R`-algebra is essentially of finite presentation
over `R`. -/
theorem EssFinitePresentation.of_isLocalization
    (P : Type w) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (M : Submonoid P) [IsLocalization M S] :
    EssFinitePresentation R S := by
  sorry

/-- The identity `R`-algebra is essentially of finite presentation over `R`. -/
instance : EssFinitePresentation R R :=
  inferInstance

/-- Essential finite presentation is preserved by `R`-algebra equivalence. -/
theorem EssFinitePresentation.equiv (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] (e : S ≃ₐ[R] T) : EssFinitePresentation R T := by
  sorry

/-- Essential finite presentation is preserved by base change. -/
instance EssFinitePresentation.baseChange (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] : EssFinitePresentation T (T ⊗[R] S) := by
  sorry

/-- Composition preserves essential finite presentation. -/
theorem EssFinitePresentation.trans {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : EssFinitePresentation R S) (hST : EssFinitePresentation S T) :
    EssFinitePresentation R T := by
  sorry

/-- Essentially finitely presented algebras are essentially of finite type. -/
theorem EssFinitePresentation.toEssFiniteType (h : EssFinitePresentation R S) :
    EssFiniteType R S := by
  sorry

/-- Essentially finitely presented algebras are essentially of finite type. -/
instance [EssFinitePresentation R S] : EssFiniteType R S :=
  EssFinitePresentation.toEssFiniteType R S inferInstance

end Algebra

namespace RingHom

/-- A ring homomorphism presents its target as a localization of a quotient of its source. -/
def IsLocalizationOfQuotient (f : R →+* S) : Prop :=
  ∃ (I : Ideal R) (_ : Algebra (R ⧸ I) S) (M : Submonoid (R ⧸ I))
    (_ : IsLocalization M S),
      f = (algebraMap (R ⧸ I) S).comp (Ideal.Quotient.mk I)

/-- Definition 10.54.1 (2): a ring homomorphism `R → S` is essentially of finite presentation if
the corresponding `R`-algebra is essentially of finite presentation. -/
@[algebraize Algebra.EssFinitePresentation]
def EssFinitePresentation (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFinitePresentation R S

/-- Unfolding `RingHom.EssFinitePresentation` gives the standard localization-of-a-finitely-
presented-source-algebra condition. -/
theorem essFinitePresentation_iff (f : R →+* S) :
    f.EssFinitePresentation ↔
      letI := f.toAlgebra
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := by
  letI := f.toAlgebra
  rw [RingHom.EssFinitePresentation]
  exact Algebra.essFinitePresentation_iff R S

/-- Unfolding `RingHom.EssFinitePresentation` gives the standard factorization of `f` as a
finitely presented ring map followed by a localization. -/
theorem essFinitePresentation_iff_exists_finitePresentation (f : R →+* S) :
    f.EssFinitePresentation ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
        (M : Submonoid P) (_ : Algebra P S) (_ : IsLocalization M S),
        f = (algebraMap P S).comp g := by
  constructor
  · intro hf
    rw [essFinitePresentation_iff] at hf
    letI := f.toAlgebra
    rcases hf with ⟨P, _, _, _, _, hP, M, hloc⟩
    refine ⟨P, inferInstance, algebraMap R P, ?_, M, inferInstance, hloc, ?_⟩
    · rw [finitePresentation_algebraMap]
      exact hP
    · simpa [RingHom.algebraMap_toAlgebra] using (IsScalarTower.algebraMap_eq R P S)
  · rintro ⟨P, _, g, hg, M, _, hloc, hgS⟩
    subst hgS
    letI := g.toAlgebra
    letI : Algebra R S := ((algebraMap P S).comp g).toAlgebra
    have hP : Algebra.FinitePresentation R P := by
      rw [← finitePresentation_algebraMap]
      exact hg
    letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' rfl
    rw [essFinitePresentation_iff]
    exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, hP, M, hloc⟩

@[simp]
theorem essFinitePresentation_algebraMap [Algebra R S] :
    (algebraMap R S).EssFinitePresentation ↔ Algebra.EssFinitePresentation R S := by
  rw [RingHom.EssFinitePresentation, toAlgebra_algebraMap]

namespace EssFinitePresentation

/-- The identity ring map is essentially of finite presentation. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssFinitePresentation := by
  change Algebra.EssFinitePresentation R R
  infer_instance

end EssFinitePresentation

end RingHom

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

/-- Composition preserves essential finite presentation. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssFinitePresentation)
    (hg : g.EssFinitePresentation) : (g.comp f).EssFinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFinitePresentation.trans R S hf hg

/-- Essential finite presentation is stable under composition. -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.EssFinitePresentation :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg

/-- Essential finite presentation is stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.EssFinitePresentation := by
  refine .mk (stableUnderComposition.respectsIso fun {R S} _ _ e ↦ ?_) ?_
  · algebraize [e.toRingHom]
    simpa using
      (Algebra.EssFinitePresentation.equiv R R S <| AlgEquiv.ofRingEquiv (congrFun rfl))
  · introv h
    rw [essFinitePresentation_algebraMap] at h ⊢
    letI : Algebra.EssFinitePresentation R T := h
    infer_instance

end RingHom.EssFinitePresentation
