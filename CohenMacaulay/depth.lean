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
