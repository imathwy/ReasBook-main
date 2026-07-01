import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the chapter's `J-0`/`J-1`/`J-2` hierarchy for Noetherian rings and its
  fraction-field / residue-field bridge criteria;
- sampled owner declarations of the same kind:
  `IsJ0Ring`,
  `IsJ1Ring`,
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`;
- best owner abstraction: this file is `source-facing`, but its public API should still be
  organized around the existing owners `IsJ0Ring`, `IsJ1Ring`, and `IsJ2Ring` from
  `Definition_15_47_1`, while the residue-field clause should use the canonical prime-ideal owner
  `p : Ideal R` with `[p.IsPrime]` and `p.ResidueField` rather than a `PrimeSpectrum` wrapper;
- primitive vs. derived: the primitive data in conditions `(2)` and `(3)` are the finite type /
  finite `R`-algebra structures together with the domain hypothesis in `(2)`. Noetherianity of
  those target rings is derived from the owner conclusions `IsJ0Ring A` and `IsJ1Ring A`, so it
  should not remain primitive public data in this `TFAE` statement. Likewise, the prime-spectrum
  presentation of condition `(4)` is derived from the prime ideal and should not stay as the
  algebra-facing owner surface. The `R`-algebra structure on a residue-field extension
  `L / p.ResidueField` is derived internal data coming from `R → p.ResidueField → L`, so it should
  not be exposed as a primitive binder in the public clause. For the witness algebra in `(4)`,
  the source-faithful primitive witness data are that `A` is a finite `R`-algebra domain with
  `IsFractionRing A L` and `IsJ0Ring A`; the domain hypothesis is not derivable from
  `IsFractionRing A L` in mathlib, so it must remain explicit in the public clause.
-/

-- Proof sketch: `(1) → (2)` and `(1) → (3)` follow by applying the defining `J-2` property to
-- finite type and finite `R`-algebras, with the domain case giving `J-0` because a domain that is
-- `J-1` is `J-0`. For `(2) → (1)`, apply Lemma `15.47.3` to each prime quotient of a finite type
-- `R`-algebra. The implication `(3) → (4)` is obtained by applying `(3)` to the finite
-- `R`-algebra whose fraction field is the given purely inseparable residue-field extension, while
-- `(4) → (2)` follows by replacing the fraction field of a finite type domain algebra by a finite
-- purely inseparable/separable tower as in Lemma `10.42.4`, choosing a `J-0` model over the
-- residue field, and descending `J-0` back along Lemmas `15.47.5` and `15.47.4`.
/-- Lemma 15.47.6: for a Noetherian ring `R`, the following are equivalent: `R` is `J-2`; every
finite type `R`-algebra that is a domain is `J-0`; every finite `R`-algebra is `J-1`; and for
every prime `p` and every finite purely inseparable extension `L / κ(p)`, there exists a finite
`R`-algebra domain that is `J-0` and has fraction field `L`. -/
theorem isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
    : List.TFAE
        [ IsJ2Ring R,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A],
            IsJ0Ring A,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A],
            IsJ1Ring A,
          ∀ (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
            [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
            let _ : Algebra R L :=
              RingHom.toAlgebra
                ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
            let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
            ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
              (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
              (_ : IsFractionRing A L),
              IsJ0Ring A
        ] := sorry

end
