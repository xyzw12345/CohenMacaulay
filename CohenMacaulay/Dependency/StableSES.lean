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
  have (n : ℕ) : ∀ (L : ModuleCat.{v, u} R), (∃ (S : Set L.carrier), S.Finite ∧ Nat.card S = n ∧ Submodule.span R S = ⊤) → P L := by
    induction' n using Nat.strongRecOn with n ih
    · by_cases n_zero : n = 0
      · intro L ⟨S, SFin, card, Sspan⟩
        have empty : S = ∅ := Set.isEmpty_coe_sort.1 <|
          (@Finite.card_eq_zero_iff _ SFin).1 <| nonpos_iff_eq_zero.1
            <| by rw [card, n_zero]
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
      · intro L ⟨S, SFin, card_eq, Sspan⟩
        let m : ℕ := sorry
        have card_eq' : Nat.card S = m + 1 := sorry
        have m_le_n : m < n := sorry
        rcases Set.eq_insert_of_ncard_eq_succ card_eq' with ⟨s, T, sT, ins, Tcard⟩
        have PT : P (ModuleCat.of R (Submodule.span R T)) := by
          refine ih m m_le_n (ModuleCat.of R (Submodule.span R T)) ?_
          haveI TFin : T.Finite := by
            refine Set.finite_of_ncard_ne_zero ?_
            rw [Tcard]
            sorry
          haveI : Fintype T := Set.Finite.fintype TFin
          set f : T → Submodule.span R T := fun t : T ↦ by
            use t
            sorry
          refine ⟨Set.range f, Set.finite_range f, ?_⟩
          constructor
          · sorry
          · have : Set.range f = {t : Submodule.span R T | (t : L) ∈ T} := by
              ext t
              constructor <;> intro ht
              · rcases Subtype.exists.mp <| Set.mem_range.mp ht with ⟨_, b, feq⟩
                exact Set.mem_of_eq_of_mem (id (Eq.symm feq)) b
              · exact Set.mem_range.mp <| Subtype.exists.mpr ⟨t, ht, rfl⟩
            simp only [this, Submodule.span_setOf_mem_eq_top]
        sorry
  sorry

example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S T : Set M) (a : M)
  (hins : insert a T = S) (hspan : Submodule.span R S = ⊤) :
    Submodule.span R {Submodule.Quotient.mk a} =
      (⊤ : Submodule R (M ⧸ Submodule.span R T)) := by
  ext x
  constructor
  · intro h
    simp only [Submodule.mem_top]
  · intro h
    rw [Submodule.mem_span]
    intro p hp
    simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hp

    sorry
end ModuleCat
