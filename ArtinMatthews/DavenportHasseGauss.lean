module

public import ArtinMatthews.WeightedMonicEuler
public import ArtinMatthews.DavenportHasseLinearRecurrence
public import ArtinMatthews.DavenportHassePrimePowerTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The Davenport--Hasse lifting identity, derived from the actual
weighted monic factorization recurrence and the exact norm/trace fiber
counts. No Gauss lifting formula is assumed. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem polynomialWeight_primePowerTrace (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (n : ℕ) :
    primePowerTrace (polynomialWeight χ ψ) (n+1) =
      (-1 : ℂ)^n * (gaussSum χ ψ)^(n+1) := by
  have hc (k : ℕ) : WeightedMonic.coefficient (polynomialWeight χ ψ) k =
      linearCoefficient (gaussSum χ ψ) k :=
    (degreeCoefficient_monic_sum χ ψ k).symm.trans (degreeCoefficient_linear χ hχ ψ k)
  apply linearCoefficient_recurrence_solution
  intro k
  simpa only [hc] using
    (WeightedMonic.coefficient_recurrence (polynomialWeight χ ψ)
      (polynomialWeight_one χ ψ)
      (fun _ _ hP hQ => polynomialWeight_mul χ ψ hP hQ) k)

variable (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]

/-- Exact norm/trace Gauss lifting, including the extension-degree sign. -/
theorem gaussSum_norm_trace (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) :
    gaussSum (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.traceLift F E ψ) =
      (-1 : ℂ)^(Module.finrank F E-1) * (gaussSum χ ψ)^(Module.finrank F E) := by
  rw [lifted_gauss_eq_primePowerTrace F E χ ψ]
  have h := polynomialWeight_primePowerTrace χ hχ ψ (Module.finrank F E-1)
  rwa [Nat.sub_one_add_one_eq_of_pos Module.finrank_pos] at h

end
end ArtinMatthews.DavenportHasse
