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
noncomputable def projdim (M : ModuleCat.{v} R): WithBot ℕ∞ :=
  if HasProjectiveDimensionLT M 0 then ⊥
  else if {i: ℕ | CategoryTheory.HasProjectiveDimensionLE M i} = ∅ then ⊤
  else (↑(sInf {i: ℕ | CategoryTheory.HasProjectiveDimensionLE M i}) : ℕ∞)

noncomputable def has_finite_projdim (M : ModuleCat.{v} R): Prop :=
  ∃ h : projdim M ≠ ⊥, WithBot.unbot (projdim M) h ≠ ⊤

noncomputable def finite_projdim (M : ModuleCat.{v} R) (hfinpd : has_finite_projdim M): ℕ :=
  WithTop.untop (WithBot.unbot (projdim M) (hfinpd.1)) hfinpd.2

---lemma ring_finite_module_self : Module.Finite R (ModuleCat.of R (Shrink.{v} R)) := by
---  apply Module.Finite.self R

---Some conditions are redundant
--theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R (ModuleCat.of R (Shrink.{v} R))] [Nontrivial (ModuleCat.of R (Shrink.{v} R))] (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))] (hfinpd: has_finite_projdim M) (hfindepM: has_finite_depth M) (hfindepR: has_finite_depth (ModuleCat.of R (Shrink.{v} R))): (finite_projdim M hfinpd) + (finite_depth M hfindepM) = (finite_depth (ModuleCat.of R (Shrink.{v} R)) hfindepR) := by sorry
