import CohenMacaulay.lemma212
import CohenMacaulay.lemma213'
import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.Dependency.SMulRegular
import CohenMacaulay.depth

universe u v w

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Classical
noncomputable def projdim (M : ModuleCat.{v} R): ℕ∞ :=
  if {i: ℕ | CategoryTheory.HasProjectiveDimensionLT M i} = ∅ then
    ⊤
  else
    (↑(sInf {i: ℕ | CategoryTheory.HasProjectiveDimensionLT M i}) : ℕ∞)

noncomputable def has_finite_projdim (M : ModuleCat.{v} R): Prop := (projdim M) ≠ ⊤

noncomputable def finite_projdim (M : ModuleCat.{v} R) (hfinprojlim : has_finite_projdim M): ℕ :=
  WithTop.untop (projdim M) hfinprojlim

---Some conditions are redundant
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R (ModuleCat.of R (Shrink.{v} R))] [Nontrivial (ModuleCat.of R (Shrink.{v} R))] (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))] (hfinpd: has_finite_projdim M) (hfindepM: has_finite_depth M) (hfindepR: has_finite_depth (ModuleCat.of R (Shrink.{v} R))): (finite_projdim M hfinpd) + (finite_depth M hfindepM) = (finite_depth (ModuleCat.of R (Shrink.{v} R)) hfindepR) := by sorry
