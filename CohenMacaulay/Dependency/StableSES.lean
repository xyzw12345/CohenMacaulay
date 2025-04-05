import Mathlib

-- open CategoryTheory
-- variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]

-- class StableSES (P : C -> Prop) : Prop where
--   of_isZero : (X : C) → Limits.IsZero X → P X
--   stability : (S : ShortComplex C) -> S.ShortExact -> P (S.X₁) -> P (S.X₃) -> P (S.X₂)

-- theorem iso_trans_of_StableSES [Limits.HasZeroObject C] (P : C → Prop) [StableSES P] {X Y : C} (h : Iso X Y) : P X ↔ P Y := sorry

section ModuleCat

universe u v

variable {R : Type u} [Ring R]

theorem fg_induction (P : ModuleCat.{v, u} R → Prop)
    (h_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N)
    (h_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N)
    (h_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M), P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M)
    (M : ModuleCat.{v, u} R) (hM : Module.Finite R M) : P M := by
  have : ∃ (S : Set M.carrier), S.Finite ∧ Submodule.span R S = ⊤ := by
    apply Module.finite_def.mp at hM
    exact Submodule.fg_def.mp hM
  rcases this with ⟨S, Sfin, Sspan⟩
  have (n : ℕ) : (∃ (S : Set M.carrier), S.Finite ∧ Nat.card S = n ∧ Submodule.span R S = ⊤) → P M := by
    induction' n with h ih
    · intro ⟨S, SFin, card, Sspan⟩
      have : IsEmpty S := by
        apply (@Finite.card_eq_zero_iff _ SFin).mp card
      sorry
    · sorry



end ModuleCat
