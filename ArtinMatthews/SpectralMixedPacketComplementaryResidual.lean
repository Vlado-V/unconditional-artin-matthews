module

public import ArtinMatthews.SpectralMixedPacketComplementaryCusp
public import ArtinMatthews.SpectralABLResidualDensity
public import ArtinMatthews.SpectralInfinityResidualCross
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

/-! The same packet bound holds for the entire finite residual sector. -/

noncomputable section
open Set OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0MixedPacket_complementary_residual_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (h : SpectralEnergyTest) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ)
        (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ (n : ℤ) (hn : n ≠ 0) {B a H : ℝ}, 0 < B → 0 < a → a ≤ 1 → 0 ≤ H →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      (∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
        ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
          Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))) →
      let N := r*s
      (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j,
        ‖gamma0MixedPacketResidualTerm N h (gamma0CuspOneOver s) n hn v α m hm l j‖) ≤
        C*H*gamma0MixedPacketExceptionalSize N B n a ε (∑ j ∈ v, ‖α j‖^2) := by
  obtain ⟨C,hC,hLeft⟩ := gamma0Infinity_complementary_residual_packet_bound
  obtain ⟨c,D,hc,hD,hRight⟩ := gamma0ABLExceptional_mixed_residual_density_le 3 (by decide) hε
  let e := Real.cos (Real.pi/4)
  let K := spectralABLExceptionalBound 3/Real.pi
  let E := (|K|+D)/(4*c*e)
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨Real.sqrt C*Real.sqrt E,by positivity,?_⟩
  intro ι r s ir is hcop h v α m hm hinj n hn B a H hB ha ha₁ hH hfreq hSym
  let N := r*s
  let b := gamma0CuspOneOver s
  let S := ∑ j ∈ v, ‖α j‖^2
  let W := gamma0MixedPacketExceptionalWeight N n a ε
  let V := gamma0ResidualCosineExceptionalMoment N b n hn a
  have hW : 0 ≤ W := gamma0MixedPacketExceptionalWeight_nonneg N n ha
  have hL := hLeft N v α m hinj hm hB hfreq
  have hR := hRight r s hcop n hn a ha ha₁
  dsimp only at hR
  rw [mul_assoc D] at hR
  change c*e*V ≤ (K+D*W)/4 at hR
  have hce : 0 < c*e := mul_pos hc he
  have hRv : V ≤ E*(1+W) := by
    calc
      _ ≤ ((K+D*W)/4)/(c*e) := (le_div_iff₀ hce).mpr (by rw [mul_comm]; exact hR)
      _ ≤ (((|K|+D)*(1+W))/4)/(c*e) := by
        gcongr
        nlinarith only [le_abs_self K,hD.le,mul_nonneg (abs_nonneg K) hW]
      _ = _ := by dsimp only [E]; ring
  have hcross := gamma0Infinity_complementary_residual_cross_bound N v α m hm b n hn h ha hH hSym
  change (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j,
    ‖gamma0MixedPacketResidualTerm N h b n hn v α m hm l j‖) ≤ _
  refine hcross.trans ?_
  calc
    _ ≤ H*Real.sqrt (C*(1+B/(N : ℝ))*S)*Real.sqrt (E*(1+W)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL) hH)
        (Real.sqrt_le_sqrt hRv) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      unfold gamma0MixedPacketExceptionalSize
      rw [show C*(1+B/(N : ℝ))*S = C*(S*(1+B/(N : ℝ))) by ring,
        Real.sqrt_mul hC.le,Real.sqrt_mul hE.le]
      dsimp only [W]
      ring

end ArtinMatthews
