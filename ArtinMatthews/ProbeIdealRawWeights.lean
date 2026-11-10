module

public import ArtinMatthews.ProbePrimeRawWeights
public import ArtinMatthews.ProbeIdealRawSeries
public import ArtinMatthews.ProbeIdealEulerClassWeights
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual raw local summand on its explicit survivor enumeration. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private theorem probeIdealRawTerm_zero_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (d r k : ℕ) (hk : k = 0 ∨ k = 1) :
    probeIdealRawTerm K P χ η θ a b V (false, 2 * (d + 1), k, r) =
      probeIdealEulerZeroClassWeight K P χ (probeIdealGaussLocalVartheta K P χ η)
        θ a b V k d r := by
  have ht : 3 * (2 * (d + 1)) = 6 * (d + 1) := by omega
  have hn : 6 * (d + 1) = (6 * d + 5) + 1 := by omega
  rcases hk with rfl | rfl
  all_goals
    dsimp only [probeIdealRawTerm, probeLocalIndexDegree]
    simp only [Bool.false_eq_true, ite_false, zero_add, pow_zero, one_mul, mul_one, pow_one]
    rw [ht]
    unfold probeIdealEulerZeroClassWeight
    rw [hn, probeIdealLocalCoefficient]
    simp

private theorem probeIdealRawTerm_one_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (d r k : ℕ) (hk : k = 0 ∨ k = 1) :
    probeIdealRawTerm K P χ η θ a b V (true, 2 * d, k, r) =
      probeIdealEulerOneClassWeight K P χ (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) θ a b V k d r := by
  have ht : 1 + 3 * (2 * d) = 6 * d + 1 := by omega
  rcases hk with rfl | rfl
  all_goals
    dsimp only [probeIdealRawTerm, probeLocalIndexDegree]
    simp only [ite_true, pow_zero, pow_one, mul_one]
    rw [ht]
    unfold probeIdealEulerOneClassWeight
    rw [probeIdealLocalCoefficient]
    simp

theorem probeIdealRawTerm_survivor (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (j : ProbeLocalSurvivor) :
    probeIdealRawTerm K P χ η θ a b V (probeLocalSurvivorIndex j) =
      probeLocalSurvivorValue (Ideal.absNorm (P.asIdeal))
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6)
        (θ * b) (η * θ⁻¹ * a) V j := by
  have hphase := probeIdealEuler_phase_scalar K P χ hχ hchar η
  rcases j with r | k | ⟨d, s⟩ | d | d | ⟨d, s⟩
  · simp [probeLocalSurvivorIndex, probeIdealRawTerm, probeLocalIndexDegree,
      probeIdealLocalCoefficient_zero_zero, probeLocalSurvivorValue]
  · have hc : probeIdealLocalCoefficient K P χ 0 (k + 1) 0 = 1 := by
      simpa using probeIdealLocalCoefficient_zero_succ K P χ k 0
    simp [probeLocalSurvivorIndex, probeIdealRawTerm, probeLocalIndexDegree,
      hc, probeLocalSurvivorValue]
  · change probeIdealRawTerm K P χ η θ a b V
      (false, 2 * (d + 1), 0, d + 1 + s) = _
    rw [probeIdealRawTerm_zero_class K P χ η θ a b V d (d + 1 + s) 0 (Or.inl rfl),
      probeIdealEulerZeroClassWeight_zero K P χ hχ _ θ a b V hθ,
      ite_eq_left (by omega)]
    rfl
  · change probeIdealRawTerm K P χ η θ a b V
      (false, 2 * (d + 1), 1, d + 1) = _
    rw [probeIdealRawTerm_zero_class K P χ η θ a b V d (d + 1) 1 (Or.inr rfl),
      probeIdealEulerZeroClassWeight_one K P χ hχ hminus _ θ a b V hθ, ite_eq_left rfl]
    rfl
  · change probeIdealRawTerm K P χ η θ a b V (true, 2 * d, 0, d) = _
    rw [probeIdealRawTerm_one_class K P χ η θ a b V d d 0 (Or.inl rfl),
      probeIdealEulerOneClassWeight_zero K P χ hχ _ _ θ a b V η hθ hphase,
      ite_eq_left rfl]
    rfl
  · change probeIdealRawTerm K P χ η θ a b V
      (true, 2 * d, 1, d + 1 + s) = _
    rw [probeIdealRawTerm_one_class K P χ η θ a b V d (d + 1 + s) 1 (Or.inr rfl),
      probeIdealEulerOneClassWeight_one K P χ hχ hminus _ _ θ a b V η hθ hphase,
      ite_eq_left (by omega)]
    rfl

end

end ArtinMatthews.VaryingKummerAnalytic
