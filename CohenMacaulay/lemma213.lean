import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.FromPR.Ext0
import CohenMacaulay.lemma212
import CohenMacaulay.Dependency.SMulRegular
import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.Dependency.CategoryCenter
import Mathlib

-- set_option maxHeartbeats 2000000 in
lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R)  (f : M →ₗ[R] M₂) (h : Function.Surjective f)
    : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  refine le_antisymm (sup_le (smul_top_le_comap_smul_top I f) (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)), Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
-- set_option pp.universes true
variable {R : Type u} [CommRing R] {M N : ModuleCat.{max u v} R} {n : ℕ}
  [UnivLE.{max u v, w}]
  --[LocallySmall.{w} (ModuleCat.{max u v} R)]
  {rs : List R} (hr : IsWeaklyRegular M rs) (h : ∀ r : R, r ∈ rs → r ∈ Module.annihilator R N)

--#synth EnoughProjectives (ModuleCat.{max u v} R)

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{max u v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

-- noncomputable instance : SMul R (Ext N M n) := {
--   smul r f :=
--     let g : Ext M M 0 := Ext.mk₀ (ModuleCat.ofHom (r • (1 : M →ₗ[R] M)))
--     Ext.comp f g (add_zero n)
-- }

-- noncomputable def Ext.smulLeft : R → Ext N M n → Ext N M n :=
--   fun x => ((x • ·) : Ext N M n → Ext N M n)

-- lemma Ext.smulLeft_zero_of_ann (x : R) (hx : x ∈ Module.annihilator R N) :
--     Ext.smulLeft x = (0 : Ext N M n → Ext N M n) := by

--   sorry

-- set_option diagnostics true in
open Pointwise in
set_option maxHeartbeats 400000 in
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
          Ext.{w} N (ModuleCat.of R (QuotSMulTop r M)) n := by
        have h1 : IsWeaklyRegular (ModuleCat.of R (QuotSMulTop r M)) rs := ((isWeaklyRegular_cons_iff M r rs).mp hr).2
        have h2 : ∀ r ∈ rs, r ∈ Module.annihilator R N := fun _ hr ↦ h _ <| List.mem_cons_of_mem _ hr
        have h3 : rs.length = n := by simpa using h'
        refine AddEquiv.trans (show _ ≃ₗ[R] _ from LinearEquiv.congrRight ?_).toAddEquiv (hn h1 h2 h3)
        rw [ofList_cons]; simp only
        let f : M →ₗ[R] ((QuotSMulTop r M) ⧸ ofList rs • (⊤ : Submodule R (QuotSMulTop r M))) :=
          ((ofList rs) • (⊤ : Submodule R (QuotSMulTop r M))).mkQ ∘ₗ (r • (⊤ : Submodule R M)).mkQ
        refine (Submodule.quotEquivOfEq _ _ ?_).trans (f.quotKerEquivOfSurjective ?_)
        · unfold f
          rw [LinearMap.ker_comp, Submodule.ker_mkQ]
          rw [← Submodule.smul_top_eq_comap_smul_top_of_surjective]
          · have : r • ⊤ = span {r} • (⊤ : Submodule R M) :=
              (Submodule.ideal_span_singleton_smul r ⊤).symm
            simp [this, Submodule.sup_smul, sup_comm]
          · exact Submodule.mkQ_surjective _
        · simp only [LinearMap.coe_comp, f]
          apply Function.Surjective.comp <;> exact Submodule.mkQ_surjective _
      refine ih.trans ?_
      have h4 : IsSMulRegular M r := ((isWeaklyRegular_cons_iff M r rs).mp hr).1
      apply CategoryTheory.isoOfSubsingletonZeroMorphism
        (CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' N (IsSMulRegular.SMul_ShortComplex_exact h4) n (n + 1) rfl)
        (CategoryTheory.Abelian.Ext.covariant_sequence_exact₁' N (IsSMulRegular.SMul_ShortComplex_exact h4) n (n + 1) rfl)
        (Iso.refl _) (Iso.refl _) (by aesop_cat) h_left_subsingleton
      dsimp only
      -- dsimp [SMul_ShortComplex, Ext.postcomp]
      -- ext
      -- simp only [AddCommGrp.hom_comp, AddCommGrp.hom_ofHom, AddCommGrp.hom_zero,
      --   AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.flip_apply,
      --   Ext.bilinearComp_apply_apply, AddMonoidHom.zero_apply, id_eq]
      -- simp [postcomp]
      #check ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality
      suffices ((Ext.mk₀ (SMul_ShortComplex M r).f).postcomp N ⋯) = 0 by
        exact congrArg AddCommGrp.ofHom this
      #check (SMul_ShortComplex M r).f
      -- #check (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj N) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((shiftFunctor (HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)) (n + 1)).obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M))
      -- have lem (g' : (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj N) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((shiftFunctor (HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)) (n + 1)).obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)))
          -- := ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality g'
      -- ext (g : Abelian.Ext N M (n + 1))
      #check ((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj N) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj (((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)⟦(n+1 : ℤ)⟧))
      suffices ∀ g : ((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj N) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj (((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)⟦(n+1 : ℤ)⟧)),
          g ≫ (((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.map ((shiftFunctor (HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)) (n + 1 : ℤ)).map ((CochainComplex.singleFunctor (ModuleCat R) 0).map (ModuleCat.ofHom (r • LinearMap.id) : M ⟶ M)))) : ((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj (((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)⟦(n+1 : ℤ)⟧) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj (((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)⟦(n+1 : ℤ)⟧)))
          = ((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.map 0) by
            -- (0 : ((HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj N) ⟶ (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Q.obj (((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)⟦(n+1 : ℤ)⟧)))
            #check shiftFunctor (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).Localization (n + 1 : ℤ)
            #check shiftFunctor (HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)) (n + 1 : ℤ)
            -- ((Ext.mk₀ (SMul_ShortComplex M r).f).postcomp N ⋯) g = 0 by
            sorry

      -- unfold Abelian.Ext Localization.SmallShiftedHom Localization.SmallHom at g
      -- have g' := (equivShrink _).symm g
      -- have := ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality g'
      -- simp only [Functor.id_obj, Functor.id_map, Function.comp_apply] at this

      #check Localization.SmallShiftedHom.comp
      #check Localization.SmallShiftedHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ))

      -- rw [this]
      -- suffices ((Ext.mk₀ (SMul_ShortComplex M r).f).postcomp N ⋯) g' = 0 g' by
      --   sorry
      -- ext (g : SmallShiftedHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
      -- ((CochainComplex.singleFunctor C 0).obj N)
      -- ((CochainComplex.singleFunctor C 0).obj M) (n + 1))
      -- #check ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality g
      -- have nat := ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality g




      sorry



variable (R : Type*) [CommRing R] (r : R)

#check ((CenterZ.localizationMonoidHom (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.complex_map (ModuleCat R) (ComplexShape.up ℤ)) ∘ (CenterZ.ring_action R)) r).naturality
