module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMellin
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusZeroDetector
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative adoption of the proved quarter-line shift. With the
manuscript's D=U² and Y=U¹⁰ scales, the actual conductor and height factors
give a negative power uniformly in the manuscript zero rectangle. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section

def mobiusDetectorHeightExponent (m : ℕ) : ℝ := 1/(16*((m : ℝ)+1))

theorem mobiusDetectorHeightExponent_pos (m : ℕ) : 0 < mobiusDetectorHeightExponent m := by
  unfold mobiusDetectorHeightExponent
  positivity

theorem mobiusDetectorHeightExponent_small (m : ℕ) : mobiusDetectorHeightExponent m < 1/10 := by
  unfold mobiusDetectorHeightExponent
  have h : 1/(16*((m : ℝ)+1)) ≤ (1/16 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  linarith

theorem mobiusDetectorHeightExponent_mul (m : ℕ) :
    mobiusDetectorHeightExponent m*(m : ℝ) ≤ 1/16 := by
  have hp := (mobiusDetectorHeightExponent_pos m).le
  have h := mul_le_mul_of_nonneg_left (show (m : ℝ) ≤ (m : ℝ)+1 by linarith) hp
  have he : mobiusDetectorHeightExponent m*((m : ℝ)+1) = 1/16 := by
    unfold mobiusDetectorHeightExponent
    field_simp
  rwa [he] at h

theorem quarter_detector_power_saving (m : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    U^(3/8 : ℝ)*(U^2)^(1/2+(1/16 : ℝ))*
      (4*U^(mobiusDetectorHeightExponent m)+2)^m*(U^10)^(-(1/4 : ℝ)) ≤
        6^m*U^(-(1/2 : ℝ)) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hp : 1 ≤ U^(mobiusDetectorHeightExponent m) :=
    Real.one_le_rpow hU (mobiusDetectorHeightExponent_pos m).le
  have hh : 4*U^(mobiusDetectorHeightExponent m)+2 ≤ 6*U^(mobiusDetectorHeightExponent m) := by linarith
  have h2 : (U^2)^(1/2+(1/16 : ℝ)) = U^(9/8 : ℝ) := by
    rw [← Real.rpow_natCast_mul hU0.le 2]
    congr 1
    norm_num
  have h10 : (U^10)^(-(1/4 : ℝ)) = U^(-(5/2 : ℝ)) := by
    rw [← Real.rpow_natCast_mul hU0.le 10]
    congr 1
    norm_num
  calc
    _ ≤ U^(3/8 : ℝ)*(U^2)^(1/2+(1/16 : ℝ))*
        (6*U^(mobiusDetectorHeightExponent m))^m*(U^10)^(-(1/4 : ℝ)) := by gcongr
    _ = 6^m * (U^(3/8 : ℝ)*U^(9/8 : ℝ)*
        U^(mobiusDetectorHeightExponent m*(m : ℝ))*U^(-(5/2 : ℝ))) := by
      rw [h2,h10,mul_pow,← Real.rpow_mul_natCast hU0.le]
      ring
    _ = 6^m*U^((3/8 : ℝ)+9/8+mobiusDetectorHeightExponent m*(m : ℝ)-5/2) := by
      rw [← Real.rpow_add hU0,← Real.rpow_add hU0,← Real.rpow_add hU0]
      congr 2
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by linarith [mobiusDetectorHeightExponent_mul m])) (by positivity)

theorem exists_actual_mobius_zero_detector_power_saving
    (K : Type*) [Field K] [NumberField K] :
    ∃ r C : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        ∀ ρ : ℂ, (249/250 : ℝ) ≤ ρ.re → |ρ.im| ≤ 4*U^r →
          ψ.primitiveContinued hM hprim ρ=0 →
          ‖ψ.mobiusSmoothedSum (U^2) ρ (U^10)‖ ≤ C*U^(-(1/2 : ℝ)) := by
  obtain ⟨C,m,hC,hbound⟩ := exists_actual_mobius_zero_detector_bound K (1/16) (by norm_num)
  refine ⟨mobiusDetectorHeightExponent m,C*6^m,mobiusDetectorHeightExponent_pos m,
    mobiusDetectorHeightExponent_small m,mul_pos hC (by positivity),?_⟩
  intro U hU M ψ hM hprim hnp hMU ρ hρ him hz
  have H := hbound ψ hM hprim hnp (U^2) (U^10) (one_le_pow₀ hU) (one_le_pow₀ hU)
    ρ (by linarith : (3/4 : ℝ) ≤ ρ.re) hz
  calc
    _ ≤ C*U^(3/8 : ℝ)*(U^2)^(1/2+(1/16 : ℝ))*
        (4*U^(mobiusDetectorHeightExponent m)+2)^m*(U^10)^(-(1/4 : ℝ)) := by
      apply H.trans
      gcongr
    _ = C*(U^(3/8 : ℝ)*(U^2)^(1/2+(1/16 : ℝ))*
        (4*U^(mobiusDetectorHeightExponent m)+2)^m*(U^10)^(-(1/4 : ℝ))) := by ring
    _ ≤ C*(6^m*U^(-(1/2 : ℝ))) := mul_le_mul_of_nonneg_left (quarter_detector_power_saving m hU) hC.le
    _ = _ := by ring

theorem exists_actual_mobius_zero_detector_eventually_small
    (K : Type*) [Field K] [NumberField K] :
    ∃ r U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        ∀ ρ : ℂ, (249/250 : ℝ) ≤ ρ.re → |ρ.im| ≤ 4*U^r →
          ψ.primitiveContinued hM hprim ρ=0 →
          ‖ψ.mobiusSmoothedSum (U^2) ρ (U^10)‖ ≤ 1/8 := by
  obtain ⟨r,C,hr,hr',_hC,hbound⟩ := exists_actual_mobius_zero_detector_power_saving K
  have hlim : Tendsto (fun U : ℝ => C*U^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul C
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/8)))
  refine ⟨r,max 2 U₀,hr,hr',le_max_left _ _,?_⟩
  intro U hU M ψ hM hprim hnp hMU ρ hρ him hz
  have hU1 : 1 ≤ U := by linarith [le_max_left (2 : ℝ) U₀]
  exact (hbound U hU1 ψ hM hprim hnp hMU ρ hρ him hz).trans
    (hU₀ U (le_trans (le_max_right _ _) hU)).le

end
end ArtinMatthews.VaryingKummerAnalytic
