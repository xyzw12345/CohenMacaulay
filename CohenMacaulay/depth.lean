import CohenMacaulay.lemma212
import CohenMacaulay.lemma213'
import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.Dependency.SMulRegular

universe u v w

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Classical
noncomputable def depth [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)(M : ModuleCat.{v} R) [Module.Finite R M] [Small.{v} (R ⧸ I)]: WithBot ℕ∞ :=
  if {i: ℕ | ¬Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)} = ∅ then
    sorry
  else
    (↑(sInf {i: ℕ | ¬Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)}) : WithBot ℕ∞)

/- -- depth in finite case?
noncomputable def natDepth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] : ℕ :=
  have h : ∃ i : ℕ,
    ¬ Subsingleton (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) M i) := sorry
  Nat.find h
 -/

theorem exist_nontrivial_ext [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] : ∃ i : ℕ,
    Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) M i) := sorry

theorem depth_eq_nat_find [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] :
    depth (IsLocalRing.maximalIdeal R) M = Nat.find (exist_nontrivial_ext M) := sorry
