import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.FromPR.Ext0
import CohenMacaulay.Dependency.SMulRegular
import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.Dependency.ExtLemma
import Mathlib.RingTheory.Regular.RegularSequence

lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R)  (f : M →ₗ[R] M₂) (h : Function.Surjective f)
    : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  refine le_antisymm (sup_le (smul_top_le_comap_smul_top I f) (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)), Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
variable {R : Type u} [CommRing R] {M N : ModuleCat.{max u v} R} {n : ℕ}
  [UnivLE.{max u v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

lemma ext_hom_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    (AddCommGrp.ofHom ((Ext.mk₀ <| ModuleCat.ofHom (r • (LinearMap.id (M := M)))).postcomp N (add_zero n))) = 0 := by
  have : (Linear.toCatCenter R (ModuleCat R) r).app N = 0 := by
    ext x; simpa using (Module.mem_annihilator.mp mem_ann x)
  apply congrArg AddCommGrp.ofHom
  apply (CategoryTheory.homCommute M N (Linear.toCatCenter R (ModuleCat R) r) n).trans ?_
  simp [this]
