module

public import ArtinMatthews.ProbePrimeRawSeries
public import ArtinMatthews.ProbeEulerClassWeights


set_option backward.privateInPublic true
@[expose] public section

/-! The actual raw local summand on its explicit survivor enumeration. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

def probeLocalSurvivorValue (q R W D V : ℂ) : ProbeLocalSurvivor → ℂ
  | .inl r => V ^ r
  | .inr (.inl k) => W ^ (k + 1)
  | .inr (.inr (.inl (d, s))) => R ^ (d + 1) * (1 - q⁻¹) * V ^ (d + 1 + s)
  | .inr (.inr (.inr (.inl d))) => R ^ (d + 1) * W * V ^ (d + 1)
  | .inr (.inr (.inr (.inr (.inl d)))) => -D * R ^ d * V ^ d
  | .inr (.inr (.inr (.inr (.inr (d, s))))) =>
      -D * W * R ^ d * (q - 1) * V ^ (d + 1 + s)

variable (K : Type*) [Field K] [NumberField K]

private theorem probePrimeRawTerm_zero_class (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (d r k : ℕ) (hk : k = 0 ∨ k = 1) :
    probePrimeRawTerm K p hp χ η θ a b V (false, 2 * (d + 1), k, r) =
      probeEulerZeroClassWeight K p hp χ (probePrimeGaussLocalVartheta K p hp χ η)
        θ a b V k d r := by
  have ht : 3 * (2 * (d + 1)) = 6 * (d + 1) := by omega
  have hn : 6 * (d + 1) = (6 * d + 5) + 1 := by omega
  rcases hk with rfl | rfl
  all_goals
    dsimp only [probePrimeRawTerm, probeLocalIndexDegree]
    simp only [Bool.false_eq_true, ite_false, zero_add, pow_zero, one_mul, mul_one, pow_one]
    rw [ht]
    unfold probeEulerZeroClassWeight
    rw [hn, probePrimeLocalCoefficient]
    simp

private theorem probePrimeRawTerm_one_class (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (d r k : ℕ) (hk : k = 0 ∨ k = 1) :
    probePrimeRawTerm K p hp χ η θ a b V (true, 2 * d, k, r) =
      probeEulerOneClassWeight K p hp χ (probePrimeGaussGamma K p hp χ 2)
        (probePrimeGaussLocalVartheta K p hp χ η) θ a b V k d r := by
  have ht : 1 + 3 * (2 * d) = 6 * d + 1 := by omega
  rcases hk with rfl | rfl
  all_goals
    dsimp only [probePrimeRawTerm, probeLocalIndexDegree]
    simp only [ite_true, pow_zero, pow_one, mul_one]
    rw [ht]
    unfold probeEulerOneClassWeight
    rw [probePrimeLocalCoefficient]
    simp

theorem probePrimeRawTerm_survivor (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (j : ProbeLocalSurvivor) :
    probePrimeRawTerm K p hp.ne_zero χ η θ a b V (probeLocalSurvivorIndex j) =
      probeLocalSurvivorValue (Ideal.absNorm (Ideal.span {p}))
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6)
        (θ * b) (η * θ⁻¹ * a) V j := by
  have hphase := probePrimeEuler_phase_scalar K p hp χ hχ hchar η
  rcases j with r | k | ⟨d, s⟩ | d | d | ⟨d, s⟩
  · simp [probeLocalSurvivorIndex, probePrimeRawTerm, probeLocalIndexDegree,
      probePrimeLocalCoefficient_zero_zero, probeLocalSurvivorValue]
  · have hc : probePrimeLocalCoefficient K p hp.ne_zero χ 0 (k + 1) 0 = 1 := by
      simpa using probePrimeLocalCoefficient_zero_succ K p hp χ k 0
    simp [probeLocalSurvivorIndex, probePrimeRawTerm, probeLocalIndexDegree,
      hc, probeLocalSurvivorValue]
  · change probePrimeRawTerm K p hp.ne_zero χ η θ a b V
      (false, 2 * (d + 1), 0, d + 1 + s) = _
    rw [probePrimeRawTerm_zero_class K p hp.ne_zero χ η θ a b V d (d + 1 + s) 0 (Or.inl rfl),
      probeEulerZeroClassWeight_zero K p hp χ hχ _ θ a b V hθ,
      ite_eq_left (by omega)]
    rfl
  · change probePrimeRawTerm K p hp.ne_zero χ η θ a b V
      (false, 2 * (d + 1), 1, d + 1) = _
    rw [probePrimeRawTerm_zero_class K p hp.ne_zero χ η θ a b V d (d + 1) 1 (Or.inr rfl),
      probeEulerZeroClassWeight_one K p hp χ hχ hminus _ θ a b V hθ, ite_eq_left rfl]
    rfl
  · change probePrimeRawTerm K p hp.ne_zero χ η θ a b V (true, 2 * d, 0, d) = _
    rw [probePrimeRawTerm_one_class K p hp.ne_zero χ η θ a b V d d 0 (Or.inl rfl),
      probeEulerOneClassWeight_zero K p hp χ hχ _ _ θ a b V η hθ hphase,
      ite_eq_left rfl]
    rfl
  · change probePrimeRawTerm K p hp.ne_zero χ η θ a b V
      (true, 2 * d, 1, d + 1 + s) = _
    rw [probePrimeRawTerm_one_class K p hp.ne_zero χ η θ a b V d (d + 1 + s) 1 (Or.inr rfl),
      probeEulerOneClassWeight_one K p hp χ hχ hminus _ _ θ a b V η hθ hphase,
      ite_eq_left (by omega)]
    rfl

end

end ArtinMatthews.VaryingKummerAnalytic
