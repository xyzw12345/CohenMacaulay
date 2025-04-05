import Mathlib
import «CohenMacaulay».Dependency.StableSES

/-!
# Missing lemmas in Mathlib of Associated Prime
-/

universe u v
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

section helper

variable (N : Submodule R M)

private theorem RelSeries_smash_helper {α : Type*} {r : α → α → Prop} {s : α → α → Prop}
    (p : RelSeries r) (q : RelSeries r) (connect : p.last = q.head)
    (hp : ∀ (i : Fin p.length), s (p (Fin.castSucc i)) (p i.succ))
    (hq : ∀ (i : Fin q.length), s (q (Fin.castSucc i)) (q i.succ)) :
    ∀ (i : Fin (RelSeries.smash p q connect).length), s ((RelSeries.smash p q connect) (Fin.castSucc i)) ((RelSeries.smash p q connect) i.succ) := by
  let p' : RelSeries (r ⊓ s) := ⟨p.length, p.toFun, fun i ↦ ⟨p.step i, hp i⟩⟩
  let q' : RelSeries (r ⊓ s) := ⟨q.length, q.toFun, fun i ↦ ⟨q.step i, hq i⟩⟩
  let pq' : RelSeries (r ⊓ s) := RelSeries.smash p' q' connect
  exact fun i ↦ (pq'.step i).2

def submodule_equiv (N1 N2 : Submodule R N) : ((Submodule.map N.subtype N1) ⧸
    Submodule.comap (Submodule.map N.subtype N1).subtype (Submodule.map N.subtype N2))
    ≃ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 := by
  refine Submodule.Quotient.equiv
    (Submodule.comap (Submodule.map N.subtype N1).subtype (Submodule.map N.subtype N2))
    (Submodule.comap N1.subtype N2) (N.equivSubtypeMap N1).symm ?_
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨a, ⟨⟨haN, haN1⟩, ⟨_, haN2⟩, rfl⟩⟩
    exact haN2
  · intro hx
    refine ⟨x.1, ⟨x.1.2, x.2⟩, ⟨⟨x.1.2, hx⟩, rfl⟩⟩

noncomputable def mkQ_equiv (N1 N2 : Submodule R (M ⧸ N)) : ((Submodule.comap N.mkQ N1) ⧸
    Submodule.comap (Submodule.comap N.mkQ N1).subtype (Submodule.comap N.mkQ N2))
    ≃ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 := by
  let f : (Submodule.comap N.mkQ N1) →ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 :=
    (Submodule.comap N1.subtype N2).mkQ ∘ₗ N.mkQ.restrict (fun x a ↦ a)
  have : Function.Surjective f := by
    simp only [f, LinearMap.coe_comp]
    refine Function.Surjective.comp (Submodule.mkQ_surjective (Submodule.comap N1.subtype N2)) ?_
    intro x
    obtain ⟨y, hy⟩ := N.mkQ_surjective x.1
    simp only [Subtype.exists, Submodule.mem_comap, Submodule.mkQ_apply, f]
    exact ⟨y, ⟨show N.mkQ y ∈ N1 from hy ▸ x.2, Subtype.ext hy⟩⟩
  have : LinearMap.ker f = Submodule.comap (Submodule.comap N.mkQ N1).subtype (Submodule.comap N.mkQ N2) := by
    ext x; simp [f]
  rw [← this]
  exact LinearMap.quotKerEquivOfSurjective f (by assumption)

end helper

theorem exists_LTSeries_quotient_cyclic:
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := by
  let P : (ModuleCat.{v, u} R) → Prop := fun M ↦
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P))
  show P (ModuleCat.of R M)
  have P_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N := fun _ _ ↦ ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
      ⟨rfl, ⟨Submodule.eq_bot_of_subsingleton.symm, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N := by
    rintro N ⟨a, hN⟩
    by_cases htri : Nontrivial (Submodule R N)
    · refine ⟨⟨1, fun i ↦ match i with | 0 => ⊥ | 1 => ⊤,
        fun i ↦ match i with | 0 => bot_lt_top⟩, ⟨rfl, ⟨rfl, fun i ↦ ?_⟩⟩⟩
      match i with
      | 0 =>
        refine ⟨Ideal.torsionOf R N a, ⟨?_⟩⟩
        have equiv : (LinearMap.range (⊤ : Submodule R N).subtype) ≃ₗ[R]
            R ⧸ (Ideal.torsionOf R N a) := by
          rw [Submodule.range_subtype, hN]
          exact (Ideal.quotTorsionOfEquivSpanSingleton R N a).symm
        exact (LinearMap.quotKerEquivRange <| Submodule.subtype _).trans equiv
    · exact ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
      ⟨rfl, ⟨subsingleton_iff_bot_eq_top.2 <|
        not_nontrivial_iff_subsingleton.1 htri, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M), P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M := by
    rintro M N ⟨pN, hpN1, hpN2, hpN3⟩ ⟨pMN, hpMN1, hpMN2, hpMN3⟩
    let q : M →ₗ[R] M ⧸ N := Submodule.mkQ N
    let pN' : LTSeries (Submodule R M) := (LTSeries.map pN (Submodule.map (Submodule.subtype N))
      (Submodule.map_strictMono_of_injective <| Submodule.subtype_injective _))
    let pMN' : LTSeries (Submodule R M) := LTSeries.map pMN (Submodule.comap (Submodule.mkQ N))
      (Submodule.comap_strictMono_of_surjective <| Submodule.mkQ_surjective N)
    refine ⟨RelSeries.smash pN' pMN' (by simp [pN', pMN', hpN2, hpMN1]), by simp [pN', hpN1], by simp [pMN', hpMN2], ?_⟩
    apply RelSeries_smash_helper (α := Submodule R M) (s := fun M1 M2 ↦ ∃ P : Ideal R, Nonempty ((M2 ⧸ (Submodule.comap M2.subtype M1)) ≃ₗ[R] (R ⧸ P)))
    · intro i
      obtain ⟨P, ⟨hP'⟩⟩ := hpN3 i
      refine ⟨P, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pN', pMN']
      exact submodule_equiv ..
    · intro i
      obtain ⟨P, ⟨hP'⟩⟩ := hpMN3 i
      refine ⟨P, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pMN']
      exact mkQ_equiv ..
  exact fg_induction P P_zero P_base P_ext _ inferInstance

variable [IsNoetherianRing R]

theorem exists_LTSeries_quotient_iso_quotient_prime :
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, P.IsPrime ∧ Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := by
  let P : ModuleCat.{v, u} R → Prop := fun M ↦
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, P.IsPrime ∧ Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P))
  show P (ModuleCat.of R M)
  have P_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N := fun _ _ ↦ ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
    ⟨rfl, ⟨Submodule.eq_bot_of_subsingleton.symm, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M), P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M := by
    rintro M N ⟨pN, hpN1, hpN2, hpN3⟩ ⟨pMN, hpMN1, hpMN2, hpMN3⟩
    let q : M →ₗ[R] M ⧸ N := Submodule.mkQ N
    let pN' : LTSeries (Submodule R M) := (LTSeries.map pN (Submodule.map (Submodule.subtype N))
      (Submodule.map_strictMono_of_injective <| Submodule.subtype_injective _))
    let pMN' : LTSeries (Submodule R M) := LTSeries.map pMN (Submodule.comap (Submodule.mkQ N))
      (Submodule.comap_strictMono_of_surjective <| Submodule.mkQ_surjective N)
    refine ⟨RelSeries.smash pN' pMN' (by simp [pN', pMN', hpN2, hpMN1]), by simp [pN', hpN1], by simp [pMN', hpMN2], ?_⟩
    apply RelSeries_smash_helper (α := Submodule R M) (s := fun M1 M2 ↦ ∃ P : Ideal R, P.IsPrime ∧ Nonempty ((M2 ⧸ (Submodule.comap M2.subtype M1)) ≃ₗ[R] (R ⧸ P)))
    · intro i
      obtain ⟨P, hP, ⟨hP'⟩⟩ := hpN3 i
      refine ⟨P, hP, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pN', pMN']
      exact submodule_equiv ..
    · intro i
      obtain ⟨P, hP, ⟨hP'⟩⟩ := hpMN3 i
      refine ⟨P, hP, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pMN']
      exact mkQ_equiv ..
  have P_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N := by
    sorry
  exact fg_induction P P_zero P_base P_ext _ inferInstance

lemma exact_sequence_implies_associatedPrimes_cup {L M N: Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module R L] [Module R M] [Module R N] (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hexact : Function.Exact f g) : (associatedPrimes R M) ⊆ (associatedPrimes R L) ∪ (associatedPrimes R N) := by
  intro p ⟨hp, ⟨x, eq⟩⟩
  set M' := LinearMap.range (LinearMap.toSpanSingleton R M x) with hM'
  have := LinearMap.quotKerEquivRange (LinearMap.toSpanSingleton R M x)
  rw [← eq, ← hM'] at this
  -- #check LinearMap.range f
  by_cases ch : M' ⊓ LinearMap.range f = ⊥
  ·
    -- #check Submodule.subtype M'
    -- set N' :=
    sorry
  · sorry


theorem AssociatedPrimes.of_quotient_iso_quotient_prime (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) (P : Fin p.length → Ideal R) (hP : ∀ (i : Fin p.length), (P i).IsPrime ∧
    Nonempty (((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ (P i)))) :
    (associatedPrimes R M) ⊆ P '' Set.univ := by
  sorry

theorem AssociatedPrimes.finite_of_noetherian [IsNoetherianRing R] : (associatedPrimes R M).Finite := by
  sorry
