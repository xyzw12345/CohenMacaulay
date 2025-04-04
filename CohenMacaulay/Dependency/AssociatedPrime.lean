import Mathlib
import «CohenMacaulay».Dependency.StableSES

/-!
# Missing lemmas in Mathlib of Associated Prime
-/

universe u v
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem exists_LTSeries_quotient_cyclic:
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := by
  generalize h : (⊤ : Submodule R M).spanFinrank = n
  induction n generalizing M
  case zero =>
    have : (⊤ : Submodule R M).spanRank = 0 := by sorry
    refine ⟨⟨0, fun _ ↦ ⊥, Fin.elim0⟩, ⟨rfl, Eq.symm (show ⊤ = ⊥ from ?_), ?_⟩⟩
    · simpa using this
    · simp
  case succ n ih _ _ _ =>
    obtain ⟨s, hs, x, hxs⟩ : ∃ (S : {S : Set M | S.Finite}), S.2.toFinset.card = n ∧
      ∃ (x : M), (Submodule.span R (Set.insert x S.1) = ⊤) := sorry
    have h1 : (⊤ : Submodule R (Submodule.span R s.1)).spanFinrank = n := sorry
    have h2 : Module.Finite R (Submodule.span R s.1) := sorry
    have h3 : Submodule.span R s.1 < ⊤ := sorry
    obtain ⟨p', h_head', h_tail', hp'⟩ := @ih (Submodule.span R s.1) _ _ h2 h1
    use RelSeries.snoc (LTSeries.map p' (Submodule.map (Submodule.subtype (Submodule.span R s.1)))
      (Submodule.map_strictMono_of_injective <| Submodule.subtype_injective _)) ⊤ ?_
    swap
    · simpa [h_tail']
    · simp only [Set.mem_setOf_eq, RelSeries.head_snoc, LTSeries.head_map, h_head',
      Submodule.map_bot, RelSeries.last_snoc, LTSeries.last_map, id_eq, eq_mpr_eq_cast,
      RelSeries.snoc_length, LTSeries.map_length, true_and]
      intro i

      sorry





variable [IsNoetherianRing R]

theorem exists_LTSeries_quotient_iso_quotient_prime :
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, P.IsPrime ∧ Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := sorry

theorem AssociatedPrimes.of_quotient_iso_quotient_prime (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) (P : Fin p.length → Ideal R) (hP : ∀ (i : Fin p.length), (P i).IsPrime ∧
    Nonempty (((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ (P i)))) :
    (associatedPrimes R M) ⊆ P '' Set.univ := by
  sorry

theorem AssociatedPrimes.finite_of_noetherian [IsNoetherianRing R] : (associatedPrimes R M).Finite := by
  sorry
