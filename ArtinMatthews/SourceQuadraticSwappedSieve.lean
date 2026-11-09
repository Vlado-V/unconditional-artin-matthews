module

public import ArtinMatthews.SourceQuadraticRawGeneralBall
public import OAI.NumberTheory.DirichletL.CubicSieve.Operator


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite reciprocity followed by the general-exponent ball
bound. Half-unit scales are allowed, as required after division by a
common ideal. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
include htrace
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadratic_swapped_norm_bound {α : ℝ}
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B R : ℝ, 1 / 2 ≤ B → 1 / 2 ≤ R →
      ∀ rows cols : Finset E,
        (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ (q d : ℝ) ≤ 2 * B) →
        (∀ c ∈ cols, sourceReflectionIsSquarefree c ∧ (q c : ℝ) ≤ 2 * R) →
        ‖OAI.FiniteSieveOperator.operator (fun (d : rows) (c : cols) => χ d.val c.val)‖ ^ 2 ≤
          C * (B * R) ^ ε * (R + B ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hball⟩ := sourceQuadraticRawBall_of_exponent F S₀ hζ htrace hE ε hε
  let K := C * (4 : ℝ) ^ ε * (2 + (2 : ℝ) ^ α)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro B R hB hR rows cols hr hc
  have hB0 : 0 < B := by linarith
  have hR0 : 0 < R := by linarith
  let A : Matrix rows cols ℂ := fun d c => χ d.val c.val
  have ht : ‖OAI.FiniteSieveOperator.operator A‖ ^ 2 =
      ‖OAI.FiniteSieveOperator.operator A.transpose‖ ^ 2 := by
    change OAI.SevenEighths.CubicSieve.squaredNorm A =
      OAI.SevenEighths.CubicSieve.squaredNorm A.transpose
    exact (OAI.SevenEighths.CubicSieve.squaredNorm_transpose A).symm
  have hbound : ‖OAI.FiniteSieveOperator.operator A.transpose‖ ^ 2 ≤
      C * (2 * R + (2 * B) ^ α) * ((2 * R) * (2 * B)) ^ ε := by
    apply OAI.FiniteSieveOperator.squared_norm_le_of_energy _ _ (by positivity)
    intro a
    have h := hball (2 * R) (2 * B) (by linarith) (by linarith) cols rows hc hr a
    have he (c : cols) (d : rows) : A.transpose c d = χ c.val d.val :=
      sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ d.val c.val
    simpa only [he] using h
  have hterm : 2 * R + (2 * B) ^ α ≤ (2 + (2 : ℝ) ^ α) * (R + B ^ α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB0.le]
    have hx := Real.rpow_nonneg hB0.le α
    have ht := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) α
    nlinarith [mul_nonneg hR0.le ht]
  have hp : ((2 * R) * (2 * B)) ^ ε = (4 : ℝ) ^ ε * (B * R) ^ ε := by
    rw [show (2 * R) * (2 * B) = 4 * (B * R) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hB0.le hR0.le)]
  calc
    _ = ‖OAI.FiniteSieveOperator.operator A.transpose‖ ^ 2 := ht
    _ ≤ C * (2 * R + (2 * B) ^ α) * ((2 * R) * (2 * B)) ^ ε := hbound
    _ ≤ C * ((2 + (2 : ℝ) ^ α) * (R + B ^ α)) *
        ((4 : ℝ) ^ ε * (B * R) ^ ε) := by
      rw [hp]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hterm hC.le) (by positivity)
    _ = _ := by dsimp [K]; ring

end
end ArtinMatthews.SourceEulerAssembly
