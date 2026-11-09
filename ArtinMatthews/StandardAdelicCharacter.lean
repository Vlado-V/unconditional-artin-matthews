module

public import ArtinMatthews.StandardAdelicFiniteCharacter
public import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters


set_option backward.privateInPublic true
@[expose] public section

/-! The actual standard character of the number-field adele ring.
It is continuous, unitary, and trivial on the diagonally embedded field.
Finite local restrictions are trivial on the actual local integer rings. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def character : AddChar (ArchimedeanAdeles.Construction.Adeles K) ℂ where
  toFun a := archCharacter K a.1 * finiteCharacter K a.2
  map_zero_eq_one' := by
    change archCharacter K 0 * finiteCharacter K 0 = 1
    rw [AddChar.map_zero_eq_one, AddChar.map_zero_eq_one, mul_one]
  map_add_eq_mul' a b := by
    change archCharacter K (a.1+b.1) * finiteCharacter K (a.2+b.2) =
      (archCharacter K a.1 * finiteCharacter K a.2) * (archCharacter K b.1 * finiteCharacter K b.2)
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring

theorem character_continuous : Continuous (character K) :=
  ((archCharacter_continuous K).comp continuous_fst).mul ((finiteCharacter_continuous K).comp continuous_snd)

theorem character_unitary (a : ArchimedeanAdeles.Construction.Adeles K) : ‖character K a‖ = 1 := by
  change ‖archCharacter K a.1 * finiteCharacter K a.2‖ = 1
  rw [norm_mul, archCharacter_unitary, finiteCharacter_unitary, mul_one]

theorem character_principal (q : K) :
    character K (algebraMap K (ArchimedeanAdeles.Construction.Adeles K) q) = 1 := by
  change archCharacter K (algebraMap K (InfiniteAdeleRing K) q) *
    finiteCharacter K (algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q) = 1
  rw [finiteCharacter_rational]
  exact mul_inv_cancel₀ (AddChar.val_isUnit (rationalCharacter K) q).ne_zero

theorem character_arch (x : InfiniteAdeleRing K) : character K (x,0) = archCharacter K x := by
  change archCharacter K x * finiteCharacter K 0 = _
  rw [AddChar.map_zero_eq_one, mul_one]

theorem character_finite (x : ArchimedeanAdeles.Construction.FiniteAdeles K) :
    character K (0,x) = finiteCharacter K x := by
  change archCharacter K 0 * finiteCharacter K x = _
  rw [AddChar.map_zero_eq_one, one_mul]

def localFiniteCharacter (v : HeightOneSpectrum (𝓞 K)) : AddChar (v.adicCompletion K) ℂ :=
  Characters.Construction.localAdditiveCharacter K (character K) (.inr v)

theorem localFiniteCharacter_continuous (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localFiniteCharacter K v) :=
  Characters.Construction.localAdditiveCharacter_continuous K (character K) (character_continuous K) (.inr v)

theorem localFiniteCharacter_unitary (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ‖localFiniteCharacter K v x‖ = 1 := character_unitary K _

theorem localFiniteCharacter_single (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    localFiniteCharacter K v x = finiteCharacter K
      (RestrictedProduct.single (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v x) := by
  exact character_finite K _

theorem localFiniteCharacter_integral (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (hx : x ∈ v.adicCompletionIntegers K) : localFiniteCharacter K v x = 1 := by
  rw [localFiniteCharacter_single]
  apply finiteCharacter_integral
  intro w
  by_cases hw : w = v
  · subst w
    erw [RestrictedProduct.single_eq_same (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v x]
    exact hx
  · erw [RestrictedProduct.single_eq_of_ne (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) x hw]
    exact (w.adicCompletionIntegers K).zero_mem

theorem localFiniteCharacter_rational (v : HeightOneSpectrum (𝓞 K)) (q : K)
    (hq : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      algebraMap K (w.adicCompletion K) q ∈ w.adicCompletionIntegers K) :
    localFiniteCharacter K v (algebraMap K (v.adicCompletion K) q) = (rationalCharacter K q)⁻¹ := by
  rw [localFiniteCharacter_single]
  apply finiteCharacter_eq K _ q
  intro w
  change RestrictedProduct.single (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K)
    v (algebraMap K (v.adicCompletion K) q) w - algebraMap K (w.adicCompletion K) q ∈ w.adicCompletionIntegers K
  by_cases hw : w = v
  · subst w
    rw [RestrictedProduct.single_eq_same (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v
      (algebraMap K (v.adicCompletion K) q), sub_self]
    exact (v.adicCompletionIntegers K).zero_mem
  · rw [RestrictedProduct.single_eq_of_ne (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K)
      (algebraMap K (v.adicCompletion K) q) hw, zero_sub]
    exact (w.adicCompletionIntegers K).toSubring.neg_mem (hq w hw)

end
end ArtinMatthews.StandardAdelic
