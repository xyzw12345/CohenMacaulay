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
noncomputable def ideal_depth [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)(M : ModuleCat.{v} R) [Module.Finite R M] [Small.{v} (R ⧸ I)]: WithBot ℕ∞ :=
  if {i: ℕ | ¬Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)} = ∅ then
    sorry
  else
    (↑(sInf {i: ℕ | ¬Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)}) : WithBot ℕ∞)

noncomputable def depth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]: WithBot ℕ∞ := ideal_depth (IsLocalRing.maximalIdeal R) M

noncomputable def has_finite_depth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]: Prop :=
  ∃ h : depth M ≠ ⊥, WithBot.unbot (depth M) h ≠ ⊤

noncomputable def finite_depth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))] (hfindep : has_finite_depth M): ℕ :=
  WithTop.untop (WithBot.unbot (depth M) (hfindep.1)) hfindep.2

theorem depth_le_ringKrullDim_associatedPrime [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)]
    (P : associatedPrimes R M) : depth M ≤ ringKrullDim (R ⧸ P.1) := sorry

theorem depth_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] :
    depth M ≤ ringKrullDim R := sorry

theorem exist_nontrivial_ext [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] : ∃ i : ℕ,
    Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) M i) := sorry

theorem depth_eq_nat_find [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] :
    depth M = Nat.find (exist_nontrivial_ext M) := sorry
