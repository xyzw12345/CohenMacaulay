import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.FromPR.Ext0
import CohenMacaulay.FromPR.Projective
import CohenMacaulay.Dependency.SMulRegular
import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.FromPR.ExtLinear
import Mathlib

lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R)  (f : M →ₗ[R] M₂) (h : Function.Surjective f)
    : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  refine le_antisymm (sup_le (smul_top_le_comap_smul_top I f) (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)), Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
variable {R : Type u} [CommRing R] [Small.{v} R] {M N : ModuleCat.{v} R} {n : ℕ}
  [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 40000 in
lemma ext_hom_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    (AddCommGrp.ofHom <| ((Ext.mk₀ <| r • (𝟙 M))).postcomp N (add_zero n)) = 0 := by
  apply congrArg AddCommGrp.ofHom <| AddMonoidHom.ext fun h ↦ ?_
  show (((Ext.homEquiv₀_linearHom R).symm (r • 𝟙 M)).postcompOfLinear R N _) h = 0
  simp only [Ext.postcompOfLinear, Ext.bilinearCompOfLinear, Ext.homEquiv₀_linearHom,
    AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, map_smul, LinearEquiv.coe_symm_mk, homEquiv₀_hom_symm_apply,
    LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, Ext.comp_mk₀_id]
  rw [← Ext.mk₀_id_comp h]
  show r • (Ext.bilinearCompOfLinear R N N M 0 n n (zero_add n)).flip h ((Ext.homEquiv₀_linearHom R).symm (𝟙 N)) = 0
  rw [← map_smul, ← map_smul, show r • (𝟙 N) = 0 from by ext x; exact Module.mem_annihilator.mp mem_ann _]
  simp
  -- show Ext.bilinearCompOfLinear R (zero_add _)
  --   ((Ext.homEquiv₀_linearHom R).symm (r • (𝟙 (ModuleCat.of R M)))) f = 0
  -- have : (Linear.toCatCenter R (ModuleCat R) r).app N = 0 := by
  --   ext x; simpa using (Module.mem_annihilator.mp mem_ann x)
  -- apply congrArg AddCommGrp.ofHom
  -- apply (CategoryTheory.homCommute M N (Linear.toCatCenter R (ModuleCat R) r) n).trans ?_
  -- simp [this]
