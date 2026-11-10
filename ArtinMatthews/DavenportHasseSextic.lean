module

public import ArtinMatthews.ProbeSexticGaussPhase
public import ArtinMatthews.FiniteFieldNormCharacter
public import Mathlib.NumberTheory.JacobiSum.Basic
public import ArtinMatthews.DavenportHasseGauss
public import ArtinMatthews.DavenportHasseJacobi
public import ArtinMatthews.DavenportHasseNormalized
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Cubic and sextic applications of actual Davenport--Hasse lifting.
The local cubic phase has no residual extension sign. This does not
identify it with a global angular Hecke character. -/
namespace ArtinMatthews.DavenportHasse
open OAI.SevenEighths VaryingKummerAnalytic
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem character_power_ne_one {χ : MulChar F ℂ} {d j : ℕ}
    (hχ : orderOf χ = d) (hj : 0 < j) (hjd : j < d) : χ^j ≠ 1 := by
  intro he
  have hd := orderOf_dvd_iff_pow_eq_one.mpr he
  rw [hχ] at hd
  exact (Nat.not_le_of_gt hjd) (Nat.le_of_dvd hj hd)

variable (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]

theorem gaussSum_norm_trace_order_six (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (j : ℕ) (hj : 0 < j) (hj6 : j < 6) :
    gaussSum (FiniteFieldCharacter.normLift F E χ ^ j) (FiniteFieldCharacter.traceLift F E ψ) =
      (-1 : ℂ)^(Module.finrank F E-1) * (gaussSum (χ^j) ψ)^Module.finrank F E := by
  rw [← FiniteFieldCharacter.normLift_pow]
  exact gaussSum_norm_trace F E (χ^j) (character_power_ne_one hχ hj hj6) ψ

theorem jacobiSum_norm_lift_cubic (χ : MulChar F ℂ) (hχ : orderOf χ = 3) :
    jacobiSum (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.normLift F E χ) =
      (-1 : ℂ)^(Module.finrank F E-1) * (jacobiSum χ χ)^Module.finrank F E := by
  have hn : χ ≠ 1 := by intro he; simp [he] at hχ
  apply jacobiSum_norm_lift F E χ χ hn hn
  simpa only [pow_two] using character_power_ne_one hχ (j := 2) (by decide) (by decide)

theorem probeGaussGamma_norm_lift (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (j : ℕ) (hj : 0 < j) (hj6 : j < 6) :
    probeGaussGamma (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.traceLift F E ψ) j =
      (-1 : ℂ)^(Module.finrank F E-1) * probeGaussGamma χ ψ j ^ Module.finrank F E := by
  unfold probeGaussGamma
  rw [← FiniteFieldCharacter.normLift_pow]
  exact normalizedGauss_norm_trace F E (χ^j) (character_power_ne_one hχ hj hj6) ψ

theorem cubic_phase_lift_sign (m : ℕ) (hm : 0 < m) (g : ℂ) :
    -(((-1 : ℂ)^(m-1) * g^m)^3) = (-(g^3))^m := by
  have hs : ((-1 : ℂ)^(m-1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (m-1) 2, pow_mul]
    norm_num
  have hs3 : ((-1 : ℂ)^(m-1))^3 = (-1 : ℂ)^(m-1) := by
    rw [show 3 = 2+1 from rfl,pow_add,hs,pow_one,one_mul]
  have he : -((-1 : ℂ)^(m-1)) = (-1 : ℂ)^m := by
    rw [← neg_one_mul,← pow_succ',Nat.sub_one_add_one_eq_of_pos hm]
  rw [mul_pow,hs3,← neg_mul,he,neg_pow (g^3),← pow_mul,← pow_mul,Nat.mul_comm m 3]

/-- The local cubic phase commutes with norm/trace lifting, with its
extension sign canceled by the defining minus sign. -/
theorem probeGaussLocalLambda_norm_lift (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) :
    probeGaussLocalLambda (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.traceLift F E ψ) =
      probeGaussLocalLambda χ ψ ^ Module.finrank F E := by
  unfold probeGaussLocalLambda
  rw [probeGaussGamma_norm_lift F E χ hχ ψ 2 (by decide) (by decide)]
  exact cubic_phase_lift_sign _ Module.finrank_pos _

end
end ArtinMatthews.DavenportHasse
