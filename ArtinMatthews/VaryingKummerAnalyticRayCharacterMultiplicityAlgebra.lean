module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra


set_option backward.privateInPublic true
@[expose] public section

/-! Actual equal-residue ray-character quotients and their class-group
descent. Distinctness is measured on coprime ideals, not on omitted values
at bad primes in an auxiliary extension of the ideal character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenRayCharacter
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}

def sameResidueQuotient (ψ φ : EvenRayCharacter K N) (hres : ψ.residue = φ.residue) :
    EvenRayCharacter K N where
  idealHom := ψ.idealHom / φ.idealHom
  finiteOrder := by
    obtain ⟨e, he, hψ⟩ := ψ.finiteOrder
    obtain ⟨f, hf, hφ⟩ := φ.finiteOrder
    refine ⟨e * f, Nat.mul_pos he hf, fun J => ?_⟩
    have hp : ψ.idealHom J ^ (e * f) = 1 := by rw [pow_mul, hψ, one_pow]
    have hq : φ.idealHom J ^ (e * f) = 1 := by rw [Nat.mul_comm e f, pow_mul, hφ, one_pow]
    simp only [MonoidHom.div_apply, div_pow, hp, hq, one_div_one]
  residue := 1
  principalLaw := by
    intro a ha hc
    have hn : φ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) ≠ 0 := by
      rw [← φ.principalLaw a ha hc]
      exact Units.ne_zero _
    rw [MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hc)]
    change ((ψ.idealHom _ / φ.idealHom _ : ℂˣ) : ℂ) = 1
    rw [Units.val_div_eq_div_val, ψ.principalLaw a ha hc, φ.principalLaw a ha hc, hres]
    exact div_self hn

theorem sameResidueQuotient_idealHom (ψ φ : EvenRayCharacter K N)
    (hres : ψ.residue = φ.residue) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (sameResidueQuotient ψ φ hres).idealHom J = ψ.idealHom J / φ.idealHom J := rfl

theorem sameResidueQuotient_residue (ψ φ : EvenRayCharacter K N)
    (hres : ψ.residue = φ.residue) : (sameResidueQuotient ψ φ hres).residue = 1 := rfl

/-- Equality on the actual arithmetic domain of the ray characters. -/
def AgreesOnCoprimeIdeals (ψ φ : EvenRayCharacter K N) : Prop :=
  ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), IsCoprime I (rationalModulusIdeal (𝓞 K) N) →
    ψ.idealHom (integralIdealFractionalUnit I hI) = φ.idealHom (integralIdealFractionalUnit I hI)

variable [NeZero N]

def sameResidueClassCharacter (ψ φ : EvenRayCharacter K N) (hres : ψ.residue = φ.residue) :
    ClassGroup (𝓞 K) →* ℂ :=
  (sameResidueQuotient ψ φ hres).classCharacter rfl

theorem sameResidueClassCharacter_ideal (ψ φ : EvenRayCharacter K N)
    (hres : ψ.residue = φ.residue) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hc : IsCoprime I (rationalModulusIdeal (𝓞 K) N)) :
    sameResidueClassCharacter ψ φ hres (ClassGroup.mk K (integralIdealFractionalUnit I hI)) =
      (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ) /
        (φ.idealHom (integralIdealFractionalUnit I hI) : ℂ) := by
  have H := (sameResidueQuotient ψ φ hres).idealHom_eq_classValue rfl I hI hc
  change ((sameResidueQuotient ψ φ hres).classValue
    (ClassGroup.mk K (integralIdealFractionalUnit I hI)) : ℂ) = _
  simpa only [sameResidueQuotient_idealHom, Units.val_div_eq_div_val] using
    (congrArg (fun z : ℂˣ => (z : ℂ)) H).symm

/-- The actual class-character quotient records exactly the coprime-ideal
values, retaining no ghost information at the omitted bad primes. -/
theorem sameResidueClassCharacter_eq_iff_agrees (ψ φ τ : EvenRayCharacter K N)
    (hψ : ψ.residue = τ.residue) (hφ : φ.residue = τ.residue) :
    sameResidueClassCharacter ψ τ hψ = sameResidueClassCharacter φ τ hφ ↔
      AgreesOnCoprimeIdeals ψ φ := by
  constructor
  · intro h I hI hc
    have H := congrArg (fun χ : ClassGroup (𝓞 K) →* ℂ =>
      χ (ClassGroup.mk K (integralIdealFractionalUnit I hI))) h
    rw [sameResidueClassCharacter_ideal ψ τ hψ I hI hc,
      sameResidueClassCharacter_ideal φ τ hφ I hI hc] at H
    apply Units.ext
    exact (div_left_inj' (Units.ne_zero (τ.idealHom _))).mp H
  · intro h
    ext c
    rw [← classIdeal_class (K := K) (N := N) c]
    rw [sameResidueClassCharacter_ideal ψ τ hψ _ (classIdeal_ne_bot c) (classIdeal_coprime c),
      sameResidueClassCharacter_ideal φ τ hφ _ (classIdeal_ne_bot c) (classIdeal_coprime c)]
    rw [h _ (classIdeal_ne_bot c) (classIdeal_coprime c)]

end
end ArtinMatthews.VaryingKummerAnalytic.EvenRayCharacter
