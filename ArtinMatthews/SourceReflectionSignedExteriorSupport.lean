module

public import ArtinMatthews.SourceReflectionSignedExteriorProduct
public import ArtinMatthews.SourceReflectionSignedExteriorLocalSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual grouped signed exterior factor is supported on the
cleared numerator orders allowed by the reflected expansion. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "a" => sourcePrimeExponentUnit K hζ S₀
local notation "b" => fun f d => a (sourceReflectionActiveExponents K S₀ f + d)
local notation "Πext" => sourceReflectionSignedExteriorProduct K S₀ hζ hS
local notation "F" => sourceReflectionSignedExteriorLocal K S₀ hζ hS

def SourceReflectionSignedExteriorFrequencySupport (f : Finset Pr) (d : E) (ν : Kˣ) : Prop :=
  let m := ν * (b f d) ^ 2
  (∀ P : Pr, 0 ≤ exteriorPrincipalValuation P.val m) ∧
  (∀ P : Pr, exteriorPrincipalValuation P.val m % 3 ≤ 1) ∧
  ∀ P ∈ d.support, exteriorPrincipalValuation P.val m = 0

local notation "Supported" => SourceReflectionSignedExteriorFrequencySupport K S₀ hζ

theorem sourceReflectionSignedExterior_cleared_order (f : Finset Pr) (d : E)
    (hd : sourceReflectionIsSquarefree d) (hfd : Disjoint f d.support) (ν : Kˣ) (P : Pr) :
    exteriorPrincipalValuation P.val (ν * (b f d) ^ 2) =
      exteriorPrincipalValuation P.val ν + if P ∈ f ∪ d.support then 2 else 0 := by
  have hdP : d P = if P ∈ d.support then 1 else 0 := by
    by_cases hp : P ∈ d.support
    · rw [ite_eq_left hp]
      have hp' := Finsupp.mem_support_iff.mp hp
      have hle := hd P
      omega
    · rw [ite_eq_right hp]
      exact Finsupp.notMem_support_iff.mp hp
  have hb : (sourceReflectionActiveExponents K S₀ f + d) P =
      if P ∈ f ∪ d.support then 1 else 0 := by
    simp only [Finsupp.add_apply, sourceReflectionActiveExponents, Finsupp.onFinset_apply, hdP, Finset.mem_union]
    by_cases hf : P ∈ f
    · have hn : P ∉ d.support := fun hm => Finset.disjoint_left.mp hfd hf hm
      simp [hf, hn]
    · simp [hf]
  rw [exteriorPrincipalValuation_mul, exteriorPrincipalValuation_pow,
    sourceReflectionPrimeExponentUnit_order K S₀ hζ, hb]
  split_ifs <;> norm_num

theorem sourceReflectionSignedExteriorProduct_nonzero_support (h d : E) (f : Finset Pr)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support) (hfd : Disjoint f d.support)
    (ν : Kˣ) (hν : Πext (h + d) (f ∪ d.support) ν ≠ 0) : Supported f d ν := by
  let active := f ∪ d.support
  let m := ν * (b f d) ^ 2
  have hLoc (P : Pr) : F P (h + d) active ν ≠ 0 := fun hz =>
    hν (sourceReflectionSignedExteriorProduct_eq_zero_of_local_zero K S₀ hζ hS (h + d) active ν P hz)
  have hShift (P : Pr) : exteriorPrincipalValuation P.val m =
      exteriorPrincipalValuation P.val ν + if P ∈ active then 2 else 0 :=
    sourceReflectionSignedExterior_cleared_order K S₀ hζ f d hd hfd ν P
  have hOrd (P : Pr) : 0 ≤ exteriorPrincipalValuation P.val m := by
    by_contra! hn
    apply hLoc P
    rw [hShift] at hn
    by_cases hP : P ∈ active
    · rw [ite_eq_left hP] at hn
      exact sourceReflectionSignedExteriorLocal_active_zero_of_negative_order K S₀ hζ hS P
        (h + d) active ν hP (by omega)
    · rw [ite_eq_right hP] at hn
      exact sourceReflectionSignedExteriorLocal_inactive_zero_of_negative_order K S₀ hζ hS P
        (h + d) active ν hP (by omega)
  refine ⟨hOrd, ?_, ?_⟩
  · intro P
    change exteriorPrincipalValuation P.val m % 3 ≤ 1
    apply le_of_not_gt
    intro hm
    have hm₂ : exteriorPrincipalValuation P.val m % 3 = 2 := by omega
    have h₀ := hOrd P
    rw [hShift] at h₀ hm₂
    apply hLoc P
    by_cases hP : P ∈ active
    · rw [ite_eq_left hP] at h₀ hm₂
      exact sourceReflectionSignedExteriorLocal_active_zero_of_mod_three K S₀ hζ hS P
        (h + d) active ν hP (by omega) hm₂
    · rw [ite_eq_right hP, add_zero] at h₀ hm₂
      exact sourceReflectionSignedExteriorLocal_inactive_zero_of_mod_three K S₀ hζ hS P
        (h + d) active ν hP h₀ hm₂
  · intro P hP
    by_contra hn
    have hactive : P ∈ active := Finset.mem_union_right _ hP
    have hp0 := hOrd P
    rw [hShift, ite_eq_left hactive] at hp0 hn
    have hd1 : d P = 1 := by
      have hP' := Finsupp.mem_support_iff.mp hP
      have hdP := hd P
      omega
    have hh0 : h P = 0 := Finsupp.notMem_support_iff.mp
      (fun hQ => Finset.disjoint_left.mp hhd hQ hP)
    have hj : (h + d) P % 6 ≠ 4 := by simp [Finsupp.add_apply, hh0, hd1]
    exact hLoc P (sourceReflectionSignedExteriorLocal_active_zero_of_positive_cleared_order K S₀ hζ hS P
      (h + d) active ν hactive hj (by omega))

theorem sourceReflectionSignedExteriorProduct_eq_zero_of_not_supported (h d : E) (f : Finset Pr)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support) (hfd : Disjoint f d.support)
    (ν : Kˣ) (hν : ¬ Supported f d ν) : Πext (h + d) (f ∪ d.support) ν = 0 := by
  by_contra hn
  exact hν (sourceReflectionSignedExteriorProduct_nonzero_support K S₀ hζ hS h d f hd hhd hfd ν hn)

end
end ArtinMatthews.SourceEulerAssembly
