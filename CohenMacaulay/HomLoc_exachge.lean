import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.Module.LocalizedModule.Exact

open LocalizedModule
variable {R M N P: Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [AddCommGroup P] [Module R P] (S : Submonoid R)

#check LinearMap.lcomp
#check LinearMap.funLeft_injective_of_surjective

#check IsLocalizedModule.mapExtendScalars
#check IsLocalizedModule.map_exact
#check IsLocalizedModule.map_injective
#check LocalizedModule.map



lemma Hom_inj_of_surj (f : N →ₗ[R] P) (hf : Function.Surjective f) : Function.Injective (LinearMap.lcomp R M f) := sorry

def qobcue : LocalizedModule S (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N := sorry



lemma map_injective_of_surjective (f : N →ₗ[R] P) (hf : Function.Surjective f) (hinj : Function.Injective (map S (R := R) (M := M) (N := P))):
    Function.Injective (map S (R := R) (M := M) (N := N)) := sorry

lemma map_bijective_of_shortexact :
    Function.Bijective (map S (R := R) (M := M) (N := N)) := sorry

lemma map_injective_of_finite (hN : Module.Finite R N) :
    Function.Injective (map S (R := R) (M := M) (N := N)) := sorry
