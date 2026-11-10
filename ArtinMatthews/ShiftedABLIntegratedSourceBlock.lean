module

public import ArtinMatthews.ShiftedABLMellinCircle
public import ArtinMatthews.ShiftedABLMellinIntegralBound
public import ArtinMatthews.ShiftedABLMellinWilton
public import ArtinMatthews.ShiftedABLThetaSourceMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original signed circle block is bounded by the actual source
Mellin moments and the congruence-uniform Wilton coefficient estimate. -/

noncomputable section
open MeasureTheory Set OAI UpperHalfPlane
open scoped ContDiff BigOperators MatrixGroups
namespace ArtinMatthews

theorem shiftedABLThetaSignedCircleBlock_integrated
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k)
    (J : ℕ) (ν : ℝ) (hν : 0 < ν) (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T m1 m2 : ℝ)
        (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)),
        0 < m1 → 0 < m2 → 1 ≤ m1*T → 1 ≤ m2*T →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        ∀ (D m3 m4 : ℕ) [NeZero D], 0 < m4 →
        ∀ (F r L : ℕ), 0 < F → 0 < L →
        ∀ (d : ℕ × ℕ) (i : ℕ × Bool) (B : ℝ), 0 ≤ B →
        (∀ z : ℝ × ℝ, ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
          B*(1+|z.1|+|z.2|)^J *
            Real.sqrt (∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
              (fun ρ => shiftedABLSignedFrequencyIndex ρ=i),
                ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2)) →
        let Q : ℝ := 3*(L : ℝ)
        let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
        let W1 := shiftedABLThetaTestWeight g hg T m1 hT hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        ‖shiftedABLThetaSignedCircleBlock χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L d i‖ ≤
          C*‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
            ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ * B*(m1*T)*(m2*T)*
              (((2 : ℝ)^d.1)*((2 : ℝ)^d.2))^((1+ν)/2) := by
  obtain ⟨Cs,hCs,hsource⟩ := shiftedABLThetaSignedCircleBlock_source_mellin 0 (J+1) Cg hCg
  obtain ⟨Cw,hCw,hwilton⟩ := shiftedABLMellinRhoCoefficient_norm_le f hperiod χ hcoeff ν hν
  refine ⟨Cs^2*Cw,by positivity,?_⟩
  intro g hg T m1 m2 hT hgs hm1 hm2 hs1 hs2 hderiv D m3 m4 inst hm4
    F r L hF hL d i B hB hpoint Q Λ W1 W2
  obtain ⟨b1,b2,hb1,hb2,hblock⟩ := hsource χ g hg T m1 m2 hT hgs hm1 hm2 hs1 hs2
    hderiv D m3 m4 F r L hF hL d
  have hmoment1 : (∫ t : ℝ, (1+‖t‖)^(J+1)*‖b1 t‖) ≤ Cs*(m1*T) := by
    simpa only [pow_zero,one_mul] using hb1
  have hmoment2 : (∫ t : ℝ, (1+‖t‖)^(J+1)*‖b2 t‖) ≤ Cs*(m2*T) := by
    simpa only [pow_zero,one_mul] using hb2
  let K : ℝ := (((2 : ℝ)^d.1)*((2 : ℝ)^d.2))^((1+ν)/2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hper (z : ℝ × ℝ) : ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
      (B*Cw*K)*(1+|z.1|+|z.2|)^(J+1) := by
    have hw := hwilton D m3 m4 hm4 d z
      ((shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ=i))
    change Real.sqrt _ ≤ Cw*K*(1+|z.1|) at hw
    have hw' : Real.sqrt (∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
        (fun ρ => shiftedABLSignedFrequencyIndex ρ=i),
          ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2) ≤
        Cw*K*(1+|z.1|+|z.2|) := hw.trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg z.2))
            (mul_nonneg hCw.le hK))
    calc
      _ ≤ B*(1+|z.1|+|z.2|)^J * _ := hpoint z
      _ ≤ B*(1+|z.1|+|z.2|)^J * (Cw*K*(1+|z.1|+|z.2|)) :=
        mul_le_mul_of_nonneg_left hw' (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hint := shiftedABLMellin_integral_bound
    (shiftedABLMellinSignedSum χ D m3 m4 F r L d i) b1 b2 (J+1)
      (show 0 ≤ B*Cw*K by positivity) hper
  obtain ⟨_,heq⟩ := hblock i
  rw [heq,norm_mul]
  calc
    _ ≤ ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
        ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ *
        ((B*Cw*K)*(∫ t : ℝ, (1+‖t‖)^(J+1)*‖b1 t‖)*
          (∫ t : ℝ, (1+‖t‖)^(J+1)*‖b2 t‖)) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
        ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ *
        ((B*Cw*K)*(Cs*(m1*T))*(Cs*(m2*T))) := by gcongr
    _ = _ := by dsimp [K]; ring

end ArtinMatthews
