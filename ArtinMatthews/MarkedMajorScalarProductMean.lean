module

public import ArtinMatthews.MarkedMajorArcProductBudget
public import ArtinMatthews.MarkedTypeIICoefficients
public import ArtinMatthews.MarkedMajorArcProductPolynomial
public import ArtinMatthews.MarkedSparsePhaseKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorArcProductMean
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
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Translated product means for the two original scalar coefficient
polynomials, with their exact normalizations and a fixed divisor moment. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped Topology
noncomputable section

def markedMajorScalarPolynomial (S : Finset ℕ) (H : ℝ) (a : ℕ → ℂ) : ℝ → ℂ :=
  markedNaturalPolynomial S (fun n => a n/(H:ℂ))

theorem markedMajorScalarPolynomial_eq_twisted (S : Finset ℕ) (H : ℝ) (a : ℕ → ℂ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    markedMajorScalarPolynomial S H (fun n => a n*χ n) t = markedTwistedSum S a χ t/(H:ℂ) := by
  unfold markedMajorScalarPolynomial markedNaturalPolynomial markedTwistedSum
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  have ht : markedPrimePhase n t=markedLogTwist n t := by
    unfold markedPrimePhase markedLogTwist
    rw [mul_comm t (Real.log (n:ℝ)),mul_comm Complex.I]
  rw [ht]
  ring

theorem markedMajorScalarPolynomial_eq_dyadic (l r : ℕ) (U : ℝ) (a : ℕ → ℂ) :
    markedMajorScalarPolynomial (Icc l r) U a = markedDyadicPolynomial l r U a := by
  funext t
  unfold markedMajorScalarPolynomial markedNaturalPolynomial markedDyadicPolynomial
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  ring

theorem markedMajorScalarPolynomial_continuous (S : Finset ℕ) (H : ℝ) (a : ℕ → ℂ) :
    Continuous (markedMajorScalarPolynomial S H a) :=
  markedNaturalPolynomial_continuous _ _

theorem markedMajorScalarPolynomial_product_mean
    (S T : Finset ℕ) (H U A B W ξ : ℝ) (a b : ℕ → ℂ)
    (hH : 0 < H) (hU : 0 < U) (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 < W)
    (hS : ∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H)
    (hT : ∀ n ∈ T,U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U)
    (ha : ∀ m ∈ S,‖a m‖ ≤ A) (hb : ∀ n ∈ T,‖b n‖ ≤ B) :
    (∫ t in Set.Icc (-W) W,‖markedMajorScalarPolynomial S H a (t+ξ)*
      markedMajorScalarPolynomial T U b (t+ξ)‖^2) ≤ markedProductMeanEnvelope H U W A B := by
  let N := ⌊4*H*U⌋₊
  have hS₀ : ∀ m ∈ S, 0 < m := fun m hm => Nat.cast_pos.mp (hH.trans_le (hS m hm).1)
  have hT₀ : ∀ n ∈ T, 0 < n := fun n hn => Nat.cast_pos.mp (hU.trans_le (hT n hn).1)
  have hN : ∀ m ∈ S,∀ n ∈ T,m*n ≤ N := by
    intro m hm n hn
    apply (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ 4*H*U)).mpr
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*H)*(2*U) := mul_le_mul (hS m hm).2 (hT n hn).2 (Nat.cast_nonneg n) (by positivity)
      _ = _ := by ring
  have ha' : ∀ m ∈ S,‖a m/(H:ℂ)‖ ≤ A/H := by
    intro m hm
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    exact div_le_div_of_nonneg_right (ha m hm) hH.le
  have hb' : ∀ n ∈ T,‖b n/(U:ℂ)‖ ≤ B/U := by
    intro n hn
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU]
    exact div_le_div_of_nonneg_right (hb n hn) hU.le
  have hmean := markedNaturalPolynomial_product_mean_square S T
    (fun m => a m/(H:ℂ)) (fun n => b n/(U:ℂ)) N (A/H) (B/U) ξ W
    (div_nonneg hA hH.le) (div_nonneg hB hU.le) hW hS₀ hT₀ hN ha' hb'
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc] at hmean
  have hharm : (∑ d ∈ Icc 1 N,1/(d:ℝ)) ≤ 1+Real.log (N:ℝ) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log N
  have hpow := pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hharm 3
  refine hmean.trans ?_
  unfold markedProductMeanEnvelope
  change _ ≤ 8*Real.exp 1*(W+(N:ℝ))*(((A/H)*(B/U))^2*(N:ℝ)*(1+Real.log (N:ℝ))^3)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)

theorem markedMajorScalarPolynomial_product_mean_log
    (σ Cα Cβ : ℝ) (hσ : 0 ≤ σ) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S T : Finset ℕ) (H U W ξ : ℝ) (a b : ℕ → ℂ),
      0 < H → 0 < U → 0 < W → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      (∀ n ∈ T,U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U) →
      (∀ m ∈ S,‖a m‖ ≤ L^Cα) → (∀ n ∈ T,‖b n‖ ≤ L^Cβ) →
      (∫ t in Set.Icc (-W) W,‖markedMajorScalarPolynomial S H a (t+ξ)*
        markedMajorScalarPolynomial T U b (t+ξ)‖^2) ≤ C*L^(2*(Cα+Cβ)+3)*(1+W/(H*U)) := by
  let J := 1+Real.log 4+σ
  have hlog4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hJ : 0 < J := by dsimp only [J]; linarith
  refine ⟨128*Real.exp 1*J^3,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  intro S T H U W ξ a b hH hU hW hX hupper hS hT ha hb
  have hLp := zero_lt_one.trans_le hL
  have hlogX := (Real.log_le_iff_le_exp (mul_pos hH hU)).mpr hupper
  have hlog : 1+Real.log (4*H*U) ≤ J*L := by
    rw [show 4*H*U=4*(H*U) by ring,Real.log_mul (by norm_num) (mul_pos hH hU).ne']
    dsimp only [J]
    nlinarith [mul_nonneg hlog4 (sub_nonneg.mpr hL)]
  have hlog₀ : 0 ≤ 1+Real.log (4*H*U) := by
    have h4X : 1 ≤ 4*H*U := by nlinarith
    linarith [Real.log_nonneg h4X]
  have hsquare (D : ℝ) : (L^D)^2=L^(2*D) := by
    rw [mul_comm (2:ℝ),Real.rpow_mul hLp.le,Real.rpow_two]
  calc
    _ ≤ markedProductMeanEnvelope H U W (L^Cα) (L^Cβ) :=
      markedMajorScalarPolynomial_product_mean S T H U _ _ W ξ a b hH hU
        (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _) hW hS hT ha hb
    _ ≤ 128*Real.exp 1*(1+W/(H*U))*(L^Cα)^2*(L^Cβ)^2*(1+Real.log (4*H*U))^3 :=
      marked_product_mean_envelope_bound H U W _ _ hH hU hX hW.le
    _ ≤ 128*Real.exp 1*(1+W/(H*U))*(L^Cα)^2*(L^Cβ)^2*(J*L)^3 := by gcongr
    _ = _ := by
      rw [hsquare,hsquare,show 2*(Cα+Cβ)+3=2*Cα+2*Cβ+3 by ring,
        Real.rpow_add hLp,Real.rpow_add hLp,show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast]
      ring

end
end ArtinMatthews
