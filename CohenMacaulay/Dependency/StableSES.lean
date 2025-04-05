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
  have (n : ℕ) : ∀ (L : ModuleCat.{v, u} R), (∃ (S : Set L.carrier), S.Finite ∧ Nat.card S ≤ n ∧ Submodule.span R S = ⊤) → P L := by
    induction' n with n ih
    · intro L ⟨S, SFin, card, Sspan⟩
      have empty : S = ∅ := Set.isEmpty_coe_sort.1 <|
        (@Finite.card_eq_zero_iff _ SFin).1 <| nonpos_iff_eq_zero.1 card
      have h_zero_aux : Subsingleton (ModuleCat.of R (⊤ : Submodule R L)) := by
        refine {allEq a b := ?_}
        have a_prop := a.2
        have b_prop := b.2
        simp_rw [← Sspan, empty, Submodule.span_empty, Submodule.mem_bot]
          at a_prop b_prop
        rwa [← b_prop, SetLike.coe_eq_coe] at a_prop
      have h_zero₁ := h_zero (ModuleCat.of R (⊤ : Submodule R L)) h_zero_aux
      have h_zero₂ := h_zero (ModuleCat.of R (L.carrier ⧸ (⊤ : Submodule R L))) <|
        Submodule.subsingleton_quotient_iff_eq_top.2 rfl
      exact h_ext L ⊤ h_zero₁ h_zero₂
    · intro L ⟨S, SFin, card_le, Sspan⟩
      by_cases card_eq : Nat.card S = n + 1
      · rcases Set.eq_insert_of_ncard_eq_succ card_eq with ⟨s, T, sT, ins, Tcard⟩
        have PT : P (ModuleCat.of R (Submodule.span R T)) := by
          refine ih (ModuleCat.of R (Submodule.span R T)) ?_
          haveI : Fintype T := sorry
          set f : T → Submodule.span R T := fun t : T ↦ by
            use t
            sorry
          use f '' ⊤
          sorry
        sorry
      · have card_le : Nat.card S ≤ n := Nat.le_of_lt_succ <| Nat.lt_of_le_of_ne card_le card_eq
        exact ih L ⟨S, SFin, card_le, Sspan⟩
  sorry

end ModuleCat
