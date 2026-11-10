module

public import ArtinMatthews.SpectralInfinityFourierSeedPacket
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
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

/-! A single nonnegative horizontal partition gives the exact Fourier
orthogonality integral for the full compact seed and uncut wave packet. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff CompactlySupported InnerProductSpace BigOperators

namespace ArtinMatthews

theorem spectralHorizontalPartition_bounds {w : ℝ} (hw : 0 < w) (x : ℝ) :
    0 ≤ spectralHorizontalPartition w x ∧ spectralHorizontalPartition w x ≤ 1 := by
  unfold spectralHorizontalPartition
  have h : (x-w)/w ≤ x/w := div_le_div_of_nonneg_right (by linarith) hw.le
  exact ⟨sub_nonneg.mpr (Real.smoothTransition.monotone h),
    (sub_le_self _ (Real.smoothTransition.nonneg _)).trans (Real.smoothTransition.le_one _)⟩

theorem gamma0InfinityFourierSeedPacket_inner_wave {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) :
    let Ψ := gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ
    let W (z : UpperHalfPlane) := ∑ j ∈ t, α j • cuspFourierWave N (n j) (ρ j) z
    (∫ z : UpperHalfPlane, inner ℂ (Ψ.val z) (W z)) =
      (((N : ℝ)*(∑ j ∈ t, ‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) : ℝ) : ℂ) := by
  dsimp only
  let Ψ := gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ
  let ψ j := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)
  let Wj (j : ι) := cuspFourierWave N (n j) (ρ j)
  let W (z : UpperHalfPlane) := ∑ j ∈ t, α j • Wj j z
  let K (j k : ι) (z : UpperHalfPlane) := (star (α j)*α k)*inner ℂ ((ψ j).val z) (Wj k z)
  have hΨ (z : UpperHalfPlane) : Ψ.val z = ∑ j ∈ t, α j • (ψ j).val z := by
    simp only [Ψ,ψ,gamma0InfinityFourierSeedPacket,Submodule.coe_sum,Submodule.coe_smul_of_tower,
      CompactlySupportedContinuousMap.sum_apply,CompactlySupportedContinuousMap.smul_apply]
  have hEq (z : UpperHalfPlane) : inner ℂ (Ψ.val z) (W z) =
      ∑ j ∈ t, ∑ k ∈ t, K j k z := by
    rw [hΨ]
    dsimp only [W]
    rw [sum_inner]
    simp only [inner_sum,inner_smul_left,inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    change α k*((starRingEnd ℂ) (α j)*inner ℂ ((ψ j).val z) (Wj k z)) =
      ((starRingEnd ℂ) (α j)*α k)*inner ℂ ((ψ j).val z) (Wj k z)
    ring
  have hI (j k : ι) : Integrable (K j k) :=
    (spectralCompactSeed_inner_integrable (ψ j).val (Wj k)
      (cuspFourierWave_continuous N (n k) (ρ k) (hρ k).continuous)).const_mul _
  have hK (j k : ι) :
      (∫ z : UpperHalfPlane, K j k z) =
        (star (α j)*α k)*(if n j = n k then
          (N : ℂ)*(cuspFourierHeightPairing (ρ j) (ρ k) : ℂ) else 0) := by
    dsimp only [K,ψ,Wj]
    rw [integral_const_mul,cuspFourierTestSeed_inner_wave N (n j) (n k) (ρ j) (ρ k)
      (hρ j) (hcρ j) (hpρ j)]
  have hDiag (j : ι) (hj : j ∈ t) :
      (∑ k ∈ t, ∫ z : UpperHalfPlane, K j k z) =
        (((N : ℝ)*(‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [hK,ite_eq_left (show n j=n j from rfl)]
      change ((starRingEnd ℂ) (α j)*α j)*_ = _
      rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · intro k _ hkj
      rw [hK,ite_eq_right (fun he => hkj (hn he).symm),mul_zero]
  change (∫ z : UpperHalfPlane, inner ℂ (Ψ.val z) (W z)) = _
  simp_rw [hEq]
  rw [integral_finsetSum t (fun j _ => integrable_finsetSum t (fun k _ => hI j k))]
  calc
    _ = ∑ j ∈ t, ∑ k ∈ t, ∫ z : UpperHalfPlane, K j k z := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum t (fun k _ => hI j k)
    _ = ∑ j ∈ t, (((N : ℝ)*(‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) : ℝ) : ℂ) :=
      Finset.sum_congr rfl hDiag
    _ = _ := by rw [← Complex.ofReal_sum,← Finset.mul_sum]

end ArtinMatthews
