import Mathlib

open CategoryTheory
variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]

class StableSES (P : C -> Prop) : Prop where
  of_isZero : (X : C) → Limits.IsZero X → P X
  stability : (S : ShortComplex C) -> S.ShortExact -> P (S.X₁) -> P (S.X₃) -> P (S.X₂)

theorem iso_trans_of_StableSES [Limits.HasZeroObject C] (P : C → Prop) [S : StableSES P] {X Y : C} (h : Iso X Y) : P X ↔ P Y := by
  sorry

section ModuleCat

variable {R : Type*} [Ring R]

theorem fg_induction (P : ModuleCat R → Prop) [StableSES P] (h : ∀ I : Ideal R, P (ModuleCat.of R (R ⧸ I)))
    (M : ModuleCat R) (hM : Module.Finite R M) : P M := sorry

end ModuleCat
