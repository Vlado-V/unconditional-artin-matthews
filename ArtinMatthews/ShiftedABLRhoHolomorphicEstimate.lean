module

public import ArtinMatthews.ShiftedABLRhoCommonTest
public import ArtinMatthews.SourceJHolomorphicPacket
public import ArtinMatthews.ShiftedABLRhoHolomorphicSum
public import ArtinMatthews.SourceJHolomorphicPacketBound
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

/-! The literal common rho test gives a uniform absolute all-weight
holomorphic estimate for the actual signed source packet. -/
namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

theorem shiftedABLRhoCommonTest_holomorphic_packet_bound (B₀ : ℝ) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (X u : ℝ), 0 < X → X ≤ B₀ →
      ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1),
      ∀ (negative : Bool) (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) (B : ℝ),
        0 < B → Set.InjOn m (v : Set ι) → (∀ i ∈ v, (m i : ℝ) ≤ B) →
        let f := shiftedABLRhoCommonTest (4*Real.pi*X) u
        let M := C*Real.sqrt ((∑ i ∈ v, ‖α i‖^2)*(1+B/((r*s : ℕ) : ℝ)))*
          Real.sqrt (1+(n : ℝ)/((r*s : ℕ) : ℝ))
        Summable (fun j : ℕ => ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖) ∧
        (∑' j : ℕ, ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖) ≤ M ∧
        ‖sourceJHolomorphicMixedPacketSeries f r s hab negative v α m n‖ ≤ M := by
  let A := 4*Real.pi*B₀
  have hA : 0 < A := by dsimp only [A]; positivity
  obtain ⟨K,hK,hweight⟩ := shiftedABLRhoCommonTest_holomorphic_sum_bound A hA.le
  let D := spectralPeterssonDensityConstant
  have hD : 0 < D := spectralPeterssonDensityConstant_pos
  let C := K*A*Real.exp A*D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι X u hX hXB r s _ _ hcop a b hab negative v α m n B hB hm hmB f M
  let aR := 4*Real.pi*X
  have haR : 0 < aR := by dsimp only [aR]; positivity
  have hcap : aR ≤ A := mul_le_mul_of_nonneg_left hXB (by positivity)
  obtain ⟨ht,htsum⟩ := hweight aR u haR hcap
  change Summable (fun j : ℕ => ‖spectralJHolomorphicCoefficient f (2*j+2)‖) at ht
  have htotal : (∑' j : ℕ, ‖spectralJHolomorphicCoefficient f (2*j+2)‖) ≤ K*A*Real.exp A :=
    htsum.trans (mul_le_mul (mul_le_mul_of_nonneg_left hcap hK.le)
      (Real.exp_le_exp.mpr hcap) (Real.exp_nonneg _) (mul_nonneg hK.le hA.le))
  let U := Real.sqrt ((∑ i ∈ v, ‖α i‖^2)*(1+B/((r*s : ℕ) : ℝ)))
  let V := Real.sqrt (1+(n : ℝ)/((r*s : ℕ) : ℝ))
  let d := D*U*V
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg hD.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hdom (j : ℕ) : ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖ ≤
      ‖spectralJHolomorphicCoefficient f (2*j+2)‖*d :=
    sourceJHolomorphicMixedPacketTerm_norm_bound f r s hcop hab negative v α m n hB hm hmB j
  have hmajor := ht.mul_right d
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hmajor
  have hsum : (∑' j : ℕ, ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖) ≤ M := by
    calc
      _ ≤ ∑' j : ℕ, ‖spectralJHolomorphicCoefficient f (2*j+2)‖*d := hs.tsum_le_tsum hdom hmajor
      _ = (∑' j : ℕ, ‖spectralJHolomorphicCoefficient f (2*j+2)‖)*d := tsum_mul_right
      _ ≤ K*A*Real.exp A*d := mul_le_mul_of_nonneg_right htotal hd
      _ = M := by dsimp only [M,C,d,D,U,V]; ring
  exact ⟨hs,hsum,(norm_tsum_le_tsum_norm hs).trans hsum⟩

end
end ArtinMatthews
