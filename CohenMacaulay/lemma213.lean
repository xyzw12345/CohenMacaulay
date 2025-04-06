import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.FromPR.Ext0
import CohenMacaulay.lemma212
import Mathlib


lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] (I : Ideal R)  (f : M →ₗ[R] M₂) (h : Function.Surjective f)
    : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  sorry

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian
-- set_option pp.universes true
variable {R : Type u} [CommRing R] {M N : ModuleCat.{max u v} R} {n : ℕ}
  [UnivLE.{max u v, w}]
  --[LocallySmall.{w} (ModuleCat.{max u v} R)]
  {rs : List R} (hr : IsWeaklyRegular M rs) (h : ∀ r : R, r ∈ rs → r ∈ Module.annihilator R N)

--#synth EnoughProjectives (ModuleCat.{max u v} R)

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{max u v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

noncomputable instance : SMul R (Ext N M n) := {
  smul r f :=
    let g : Ext M M 0 := Ext.mk₀ (ModuleCat.ofHom (r • (1 : M →ₗ[R] M)))
    Ext.comp f g (add_zero n)
}

noncomputable def Ext.smulLeft : R → Ext N M n → Ext N M n :=
  fun x => ((x • ·) : Ext N M n → Ext N M n)

lemma Ext.smulLeft_zero_of_ann (x : R) (hx : x ∈ Module.annihilator R N) :
    Ext.smulLeft x = (0 : Ext N M n → Ext N M n) := by

  sorry

noncomputable def lemma_213 : (N →ₗ[R] M ⧸ (ofList rs • ⊤ : Submodule R M)) ≃+ Ext.{w} N M rs.length := by
  generalize h' : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff] at h'
    rw [h', ofList_nil, Submodule.bot_smul]
    let e' : (M ⧸ (⊥ : Submodule R M)) ≃ₗ[R] M := Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl
    let e : (N →ₗ[R] (M ⧸ (⊥ : Submodule R M))) ≃ₗ[R] (N →ₗ[R] M) :=
      LinearEquiv.congrRight (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl)
    let e1 : (N →ₗ[R] M) ≃+ (N ⟶ M) := AddEquiv.symm ModuleCat.homAddEquiv
    exact e.toAddEquiv.trans <| e1.trans <| (CategoryTheory.Abelian.homEquiv₀_hom N M).symm
  · have h_left_subsingleton : Subsingleton (Ext.{w} N M n) := by
      let equiv : (N →ₗ[R] M ⧸ (ofList (rs.take n) • (⊤ : Submodule R M))) ≃+ Ext.{w} N M n := by
        apply hn (M := M) (rs := rs.take n)
        · refine (RingTheory.Sequence.isWeaklyRegular_iff M _).mpr (fun i hi ↦ ?_)
          have : i < rs.length := lt_of_lt_of_le hi (List.length_take_le' n rs)
          have h1 : (List.take n rs)[i] = rs[i] := List.getElem_take
          have h2 : List.take i (List.take n rs) = List.take i rs := by
            rw [List.take_take]
            congr 1
            rw [h'] at this
            rwa [inf_eq_left, ← Nat.lt_succ_iff]
          rw [h1, h2]
          exact (RingTheory.Sequence.isWeaklyRegular_iff M rs).mp hr _ _
        · intro _ h''; exact h _ (List.mem_of_mem_take h'')
        · exact List.length_take_of_le (by rw [h']; exact Nat.le_add_right n 1)
      rw [equiv.symm.toEquiv.subsingleton_congr]
      apply lemma_212_a (r := rs[n])
      · exact (RingTheory.Sequence.isWeaklyRegular_iff M rs).mp hr ..
      · exact h _ <| List.getElem_mem _
    match rs with
    | [] => absurd h'; simp
    | r :: rs =>
      let ih : (N →ₗ[R] M ⧸ (ofList (r :: rs) • ⊤ : Submodule R M)) ≃+
          Ext.{w} N (ModuleCat.of R (M ⧸ (span {r} • (⊤ : Submodule R M)))) n := by
        have h1 : IsWeaklyRegular (ModuleCat.of R (M ⧸ (span {r} • (⊤ : Submodule R M)))) rs := sorry
        have h2 : ∀ r ∈ rs, r ∈ Module.annihilator R N := by sorry
        have h3 : rs.length = n := by simpa using h'
        refine AddEquiv.trans (show _ ≃ₗ[R] _ from LinearEquiv.congrRight ?_).toAddEquiv (hn h1 h2 h3)
        rw [ofList_cons]; simp only
        let f : M →ₗ[R] ((M ⧸ span {r} • (⊤ : Submodule R M)) ⧸ ofList rs • (⊤ : Submodule R (M ⧸ span {r} • (⊤ : Submodule R M)))) :=
          ((ofList rs) • (⊤ : Submodule R (M ⧸ span {r} • (⊤ : Submodule R M)))).mkQ ∘ₗ (span {r} • (⊤ : Submodule R M)).mkQ
        refine (Submodule.quotEquivOfEq _ _ ?_).trans (f.quotKerEquivOfSurjective ?_)
        · unfold f
          rw [LinearMap.ker_comp, Submodule.ker_mkQ]
          rw [← Submodule.smul_top_eq_comap_smul_top_of_surjective]
          · simp [Submodule.sup_smul, sup_comm]
          · exact Submodule.mkQ_surjective _
        · simp only [LinearMap.coe_comp, f]
          apply Function.Surjective.comp <;> exact Submodule.mkQ_surjective _
      -- let e : (M ⧸ ofList (r :: rs) • (⊤ : Submodule R M)) ≃ₗ[R]
      --   ((M ⧸ (span {r}) • (⊤ : Submodule R M))) ⧸ (ofList rs • (⊤ : Submodule R (M ⧸ (span {r}) • (⊤ : Submodule R M)))) := sorry
      refine ih.trans ?_

      sorry
