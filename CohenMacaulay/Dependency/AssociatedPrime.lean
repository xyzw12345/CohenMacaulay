import Mathlib
import «CohenMacaulay».Dependency.StableSES

/-!
# Missing lemmas in Mathlib of Associated Prime
-/

universe u v
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

section helper

noncomputable def quotTorsionOfEquivSpanSingleton' (x : M) (hM : ⊤ = Submodule.span R {x}) :
    ((⊤ : Submodule R M) ⧸ LinearMap.ker (⊤ : Submodule R M).subtype) ≃ₗ[R] R ⧸ Ideal.torsionOf R M x := by
  have equiv : (LinearMap.range (⊤ : Submodule R M).subtype) ≃ₗ[R]
      R ⧸ (Ideal.torsionOf R M x) := by
    rw [Submodule.range_subtype, hM]
    exact (Ideal.quotTorsionOfEquivSpanSingleton R M x).symm
  exact (LinearMap.quotKerEquivRange <| Submodule.subtype _).trans equiv

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

section calculation

open LinearMap in
lemma AssociatedPrimes.quotient_prime_eq_singleton (p : Ideal R) [hp : p.IsPrime] :
    associatedPrimes R (R ⧸ p) = {p} := by
  have h0 : ker (toSpanSingleton R (R ⧸ p) 0) = ⊤ := by simp
  have h1 (x : R ⧸ p) (h : x ≠ 0) : ker (toSpanSingleton R (R ⧸ p) x) = p := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    ext y
    simp only [mem_ker, toSpanSingleton, smulRight, id_apply]
    show (Ideal.Quotient.mk p (y * x)) = 0 ↔ y ∈ p
    simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] at h ⊢
    exact ⟨fun h' ↦ by simpa [h] using (hp.mem_or_mem h'), fun h ↦ Ideal.IsTwoSided.mul_mem_of_left x h⟩
  ext y
  simp only [associatedPrimes, IsAssociatedPrime, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, ⟨x, hx⟩⟩
    by_cases h : x = 0
    · simp_rw [h, h0] at hx
      exact False.elim (hy.1 hx)
    · exact hx.trans (h1 x h)
  · obtain ⟨x, hx⟩ : ∃ x : R ⧸ p, x ≠ 0 := exists_ne 0
    exact fun h' ↦ ⟨h' ▸ hp, ⟨x, h'.trans (h1 x hx).symm⟩⟩

end calculation

section mono

lemma associatedPrimes_mono {M : Type*} [AddCommGroup M] [Module R M] (N1 N2 : Submodule R M) (h : N1 ≤ N2):
    associatedPrimes R N1 ⊆ associatedPrimes R N2 := by
  intro p ⟨hp, ⟨x, eq⟩⟩
  constructor
  · exact hp
  · use ⟨x.1, h x.2⟩
    ext t
    simp only [eq, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact ⟨fun h' ↦ Subtype.ext <| (AddSubmonoid.mk_eq_zero N1.toAddSubmonoid).mp h',
      fun h ↦ Submodule.coe_eq_zero.mp congr($h.1)⟩

lemma associatedPrimes_subset_of_submodule {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    associatedPrimes R N ⊆ associatedPrimes R M := by
  have : associatedPrimes R M = associatedPrimes R (⊤ : Submodule R M) :=
    LinearEquiv.AssociatedPrimes.eq Submodule.topEquiv.symm
  rw [this]
  apply associatedPrimes_mono R N ⊤ (fun {x} a ↦ trivial)

end mono

section extension

lemma exact_sequence_implies_associatedPrimes_cup {L M N: Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module R L] [Module R M] [Module R N] (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (finj : Function.Injective f) (hexact : Function.Exact f g) :
    (associatedPrimes R M) ⊆ (associatedPrimes R L) ∪ (associatedPrimes R N) := by
  intro p ⟨hp, ⟨x, eq⟩⟩
  set M' := LinearMap.range (LinearMap.toSpanSingleton R M x) with hM'
  have M'_iso := LinearMap.quotKerEquivRange (LinearMap.toSpanSingleton R M x)
  rw [← eq, ← hM'] at M'_iso
  by_cases ch : M' ⊓ LinearMap.range f = ⊥
  · set N' := Submodule.map g M' with hN'
    set g_restrict : M' →ₗ[R] N' := LinearMap.restrict g (fun x a ↦ Submodule.mem_map_of_mem a) with hg
    have : Function.Bijective g_restrict := by
      constructor
      · intro a b heq
        have (x : M'): g (x : M) = g_restrict x := rfl
        have : g (a : M) = g (b : M) := by rw [this, this, heq]
        rw [← sub_eq_zero, ← LinearMap.map_sub, hexact] at this
        have : (a - b : M) ∈ M' ⊓ LinearMap.range f := ⟨sub_mem (Submodule.coe_mem a) (Submodule.coe_mem b), this⟩
        rw [ch, Submodule.mem_bot] at this
        rw [Subtype.ext_val_iff, ← sub_eq_zero, this]
      · intro y₀
        obtain ⟨x₀, x₀in, hx₀⟩ : (y₀ : N) ∈ g '' M' := Subtype.coe_prop y₀
        use ⟨x₀, x₀in⟩
        exact SetLike.coe_eq_coe.mp hx₀
    set g_iso : M' ≃ₗ[R] N' := LinearEquiv.ofBijective g_restrict this
    right
    apply associatedPrimes_subset_of_submodule R N'
    rw [← LinearEquiv.AssociatedPrimes.eq g_iso, LinearEquiv.AssociatedPrimes.eq (id M'_iso.symm),
      AssociatedPrimes.quotient_prime_eq_singleton, Set.mem_singleton_iff]
  · 
    sorry

lemma AssociatedPrimes.subset_union_of_injective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hinj : Function.Injective f) :
    associatedPrimes R N ⊆ associatedPrimes R M ∪ associatedPrimes R (N ⧸ Submodule.map f ⊤) := sorry

lemma AssociatedPrimes.subset_union_quotient {M : Type*} [AddCommGroup M] [Module R M]
    (p q : Submodule R M) (hpq : p < q) :
    (associatedPrimes R q) ⊆ (associatedPrimes R p) ∪ (associatedPrimes R (q ⧸ (Submodule.comap q.subtype p))) := by sorry

end extension

section chain

lemma AssociatedPrimes.subset_iUnion_quotient (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) : associatedPrimes R M ⊆ ⋃ i : Fin p.length,
    associatedPrimes R ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) := by
  sorry

theorem AssociatedPrimes.of_quotient_iso_quotient_prime (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) (P : Fin p.length → Ideal R) (hPprime : ∀ (i : Fin p.length), (P i).IsPrime)
    (hP : ∀ (i : Fin p.length), Nonempty
      (((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ (P i)))) :
    (associatedPrimes R M) ⊆ P '' Set.univ := by
  have heq1 : ∀ (i : Fin p.length), associatedPrimes R ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) = associatedPrimes R (R ⧸ (P i)) := by
    intro i
    let e := Classical.choice (hP i)
    exact LinearEquiv.AssociatedPrimes.eq e
  have heq1' := Set.iUnion_congr heq1
  have heq2 : ∀ (i : Fin p.length), associatedPrimes R (R ⧸ (P i)) = {P i} := by
    intro i
    exact AssociatedPrimes.quotient_prime_eq_singleton R _
  have heq2' := Set.iUnion_congr heq2
  have hmem : ⋃ i : Fin p.length, {P i} ⊆ P '' Set.univ := by
    rw[Set.iUnion_subset_iff]
    intro i
    rw [Set.image_univ, Set.singleton_subset_iff, Set.mem_range]
    use i
  apply subset_trans (AssociatedPrimes.subset_iUnion_quotient _ _ p h_head h_last)
  rw [heq1', heq2']
  exact hmem

end chain

section noetherian

variable [Module.Finite R M]

-- [Stacks 00KZ]
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
        apply quotTorsionOfEquivSpanSingleton' ..
        assumption
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
    apply RelSeries_smash_helper (α := Submodule R M) (s := fun M1 M2 ↦ ∃ P : Ideal R,
      Nonempty ((M2 ⧸ (Submodule.comap M2.subtype M1)) ≃ₗ[R] (R ⧸ P)))
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

-- [Stacks 00L0]
theorem exists_LTSeries_quotient_iso_quotient_prime [IsNoetherianRing R] :
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
    rintro N ⟨a, hN⟩
    generalize hI : Ideal.torsionOf R N a = I
    induction I using WellFoundedGT.induction generalizing N a
    rename_i I ih
    by_cases h_triv : I = ⊤
    · have : Subsingleton N := by
        rw [← Submodule.subsingleton_iff R]
        apply subsingleton_of_bot_eq_top
        simp_all
      exact P_zero N this
    · have : Nontrivial N := by
        rw [← hI, Ideal.torsionOf_eq_top_iff] at h_triv
        exact nontrivial_of_ne a 0 h_triv
      by_cases h : I.IsPrime
      · refine ⟨⟨1, fun i ↦ match i with | 0 => ⊥ | 1 => ⊤,
          fun i ↦ match i with | 0 => bot_lt_top⟩, ⟨rfl, ⟨rfl, fun i ↦ ?_⟩⟩⟩
        match i with
        | 0 =>
          refine ⟨I, h, ⟨hI ▸ ?_⟩⟩
          apply quotTorsionOfEquivSpanSingleton' ..
          assumption
      · rw [Ideal.isPrime_iff] at h
        simp only [ne_eq, h_triv, not_false_eq_true, true_and, not_forall, Classical.not_imp,
        not_or] at h
        obtain ⟨y, x, hxy, hy, hx⟩ := h
        let N' := Submodule.span R {x • a}
        apply P_ext _ N'
        · apply ih (Ideal.torsionOf R N (x • a)) ?_ (ModuleCat.of R N')
           ⟨x • a, Submodule.mem_span_singleton_self (x • a)⟩
          · ext y
            simp only [Submodule.mem_top, true_iff]
            obtain ⟨z, hz⟩ := y
            simp only [N', Submodule.mem_span_singleton] at hz ⊢
            obtain ⟨b, hb⟩ := hz
            exact ⟨b, Subtype.ext hb⟩
          · ext b
            simp
          · rw [← hI, lt_iff_le_not_le]
            constructor
            · intro z hz
              rw [Ideal.mem_torsionOf_iff] at hz ⊢
              rw [smul_smul, mul_comm, ← smul_smul, hz, smul_zero]
            · show ¬ ((Ideal.torsionOf R (↑N) (x • a)) : Set R) ⊆ (Ideal.torsionOf R (↑N) a)
              simp only [Ideal.coe_torsionOf, Set.not_subset, Set.mem_preimage,
                LinearMap.toSpanSingleton_apply, Set.mem_singleton_iff, N']
              use y
              rw [smul_smul, ← Ideal.mem_torsionOf_iff, ← Ideal.mem_torsionOf_iff, hI]
              exact ⟨hxy, hy⟩
        · refine ih (Ideal.torsionOf R (N ⧸ N') (N'.mkQ a)) ?_ (ModuleCat.of R (N ⧸ N')) (N'.mkQ a) ?_ rfl
          · rw [← hI, lt_iff_le_not_le]
            constructor
            · intro z hz
              rw [Ideal.mem_torsionOf_iff] at hz ⊢
              rw [← map_smul, hz, map_zero]
            · show ¬ ((Ideal.torsionOf R (N ⧸ N') (N'.mkQ a)) : Set R) ⊆ (Ideal.torsionOf R N a)
              simp only [Ideal.coe_torsionOf, Set.not_subset, Set.mem_preimage,
                LinearMap.toSpanSingleton_apply, Set.mem_singleton_iff, N']
              refine ⟨x, ⟨?_, by rw [← Ideal.mem_torsionOf_iff, hI]; exact hx⟩⟩
              rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
              exact Submodule.mem_span_singleton_self (x • a)
          · ext y
            simp only [Submodule.mem_top, true_iff]
            obtain ⟨z, hz⟩ := N'.mkQ_surjective y
            simp only [N', Submodule.mem_span_singleton] at ⊢
            obtain ⟨b, hb⟩ : ∃ b : R, b • a = z := by
              rw [← Submodule.mem_span_singleton, ← hN]; trivial
            exact ⟨b, by rw [← hz, ← hb, map_smul]⟩
  exact fg_induction P P_zero P_base P_ext _ inferInstance

theorem AssociatedPrimes.finite_of_noetherian [IsNoetherianRing R] : (associatedPrimes R M).Finite := by
  obtain ⟨p, h_head, h_tail, h⟩:= exists_LTSeries_quotient_iso_quotient_prime R M
  choose P h1 h2 using h
  refine Set.Finite.subset ?_ (AssociatedPrimes.of_quotient_iso_quotient_prime R M p h_head h_tail P h1 h2)
  exact Set.toFinite (P '' Set.univ)

end noetherian
