import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.lemma212
import Mathlib

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian
set_option pp.universes true
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

def lemma_213 : (N →ₗ[R] M ⧸ (ofList rs • ⊤ : Submodule R M)) ≃+ Ext.{w} N M rs.length := by
  sorry
