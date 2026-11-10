module

public import ArtinMatthews.SpectralInfinityResidualPacket
public import ArtinMatthews.SpectralABLResidualExceptionalMoment
public import ArtinMatthews.SpectralCuspExceptionalMoment
public import ArtinMatthews.SpectralInfinityResidualGap
public import ArtinMatthews.SpectralKExceptionalPhysicalTest
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! A compact physical test controls the actual finite residual packet
at infinity. The cosine is bounded below on its nonzero coefficients. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0InfinityResidualPacketMoment {ι : Type*} (N : ℕ) [NeZero N]
    (v : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0) : ℝ :=
  ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j,
    ‖gamma0InfinityResidualPacketRho N l j v α n hn‖^2/
      Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))

theorem gamma0Infinity_complementary_residual_packet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (v : Finset ι) (α : ι → ℂ) (n : ι → ℤ)
      (hn : Function.Injective n) (hn₀ : ∀ j, n j ≠ 0)
      {B : ℝ}, 0 < B → (∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) →
      gamma0InfinityResidualPacketMoment N v α n hn₀ ≤
        C*(1+B/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2) := by
  let A : ℝ := 1/4
  let c := Real.exp (-Real.exp 1)/16
  let e := Real.cos (Real.pi/4)
  have hA : 0 < A := by norm_num [A]
  have hc : 0 < c := by dsimp only [c]; positivity
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  have hE : 0 < c^2*e := by positivity
  obtain ⟨F,hF,hcF,hSupp,h01,hOne⟩ := spectralKExceptionalPhysicalTest_exists hA
  have hMass := spectralKExceptionalPhysicalTest_mass_le F hF.continuous hA hSupp h01
  refine ⟨12/(c^2*e),by positivity,?_⟩
  intro ι N inst v α n hn hn₀ B hB hfreq
  let Y := A/(2*B)
  have hY : 0 < Y := by positivity
  have hYB : Y < A/B := by
    unfold Y
    apply div_lt_div_of_pos_left hA hB
    linarith
  let κ (l : Ici (0 : ℝ)) := Real.sqrt (1/4-(l : ℝ))
  let W (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :=
    gamma0InfinityResidualPacketRho N l j v α n hn₀
  let K (l : Ici (0 : ℝ)) :=
    ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (Complex.sqrt (1/4-((l : ℝ) : ℂ))) x ∂spectralKLPhysicalMeasure
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let S := ∑ k ∈ v, ‖α k‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hP := gamma0Infinity_residual_physical_packet_bound N v α n hn hn₀ F hF hcF
    hA hB hY hYB (fun _ hx => (hSupp hx).1) hfreq
  change (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖K l*W l j‖^2) ≤
    6*(1+2*B/((N : ℝ)*A))*(M*S)/4 at hP
  have hK (l : Ici (0 : ℝ)) (hl : l ∈ gamma0ResidualEnergyWindow N) : c ≤ ‖K l‖ := by
    have hl₁ : (l : ℝ) ≤ 1/4 := ((mem_gamma0ResidualEnergyWindow N l).mp hl).1.2
    have hκ : 0 ≤ κ l := Real.sqrt_nonneg _
    have hl₀ : 0 ≤ (l : ℝ) := l.property
    have hκ₁ : κ l ≤ 1/2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
    have hPow : 1 ≤ A^(-κ l) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos hA (by norm_num [A] : A ≤ 1) (neg_nonpos.mpr hκ)
    dsimp only [K]
    rw [spectralComplexSqrt_quarter_sub_nonneg _ hl₁]
    exact (le_mul_of_one_le_right hc.le hPow).trans
      (spectralKExceptionalPhysicalTest_transform_lower F hF.continuous hA (by norm_num [A])
        hSupp (fun x => (h01 x).1) hOne hκ hκ₁)
  have hCos (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
      (hW : W l j ≠ 0) : e ≤ Real.cos (Real.pi*κ l) := by
    apply spectral_cosine_complementary_lower_of_gap
    by_contra h
    apply hW
    unfold W gamma0InfinityResidualPacketRho
    apply Finset.sum_eq_zero
    intro k _
    have hRho : gamma0ResidualABLSourceRho N l j 1 (n k) (hn₀ k) = 0 := by
      by_contra hR
      exact h (gamma0Infinity_residual_value_ge_three_sixteenths_of_rho N l j (n k) (hn₀ k) hR)
    simp [hRho]
  change (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖W l j‖^2/Real.cos (Real.pi*κ l)) ≤
    (12/(c^2*e))*(1+B/(N : ℝ))*S
  apply (mul_le_mul_iff_of_pos_left hE).mp
  calc
    _ ≤ ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖K l*W l j‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hw : W l j = 0
      · simp [hw]
      have hCos₀ := hCos l j hw
      rw [norm_mul,mul_pow]
      calc
        _ = (e/Real.cos (Real.pi*κ l))*(c^2*‖W l j‖^2) := by ring
        _ ≤ c^2*‖W l j‖^2 :=
          mul_le_of_le_one_left (by positivity) ((div_le_one (he.trans_le hCos₀)).mpr hCos₀)
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le (hK l hl) 2) (sq_nonneg _)
    _ ≤ 6*(1+2*B/((N : ℝ)*A))*(M*S)/4 := hP
    _ ≤ 6*(1+2*B/((N : ℝ)*A))*S/4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hS hMass) (by positivity)) (by norm_num)
    _ ≤ (12*(1+B/(N : ℝ)))*S := by
      have hEq : 2*B/((N : ℝ)*A) = 8*(B/(N : ℝ)) := by
        dsimp only [A]
        ring
      rw [hEq]
      calc
        _ = (6*(1+8*(B/(N : ℝ)))/4)*S := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hS
    _ = _ := by field_simp [hE.ne']

end ArtinMatthews
