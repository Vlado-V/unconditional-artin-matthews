module

public import ArtinMatthews.SpectralFrequencyTestProfile
public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralGamma0PoincareSpectral
public import ArtinMatthews.SpectralCuspWidthRefinement
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralInfinityFourierSeedMassBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The common compact physical test at infinity gives an actual ambient
packet with the same uniform orbit mass for every spectral sector. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

theorem spectralCommonFrequencyProfile_properties {ι : Type*}
    (n : ι → ℤ) (hn : ∀ j, n j ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hFB : tsupport F ⊆ Ici A) (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
    (hYB : Y < A/B) :
    let ρ (j : ι) := spectralFrequencyTestProfile |cuspFourierFrequency 1 (n j)| F
    (∀ j, ContDiff ℝ ∞ (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧
      (∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) ∧ (∀ j, tsupport (ρ j) ⊆ Ioi Y) := by
  let q (j : ι) := |cuspFourierFrequency 1 (n j)|
  let ρ (j : ι) := spectralFrequencyTestProfile (q j) F
  have hq (j : ι) : 0 < q j :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos (n j) (hn j))
  have hFp : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hFB hx)
  have hlo (j : ι) {y : ℝ} (hy : y ∈ tsupport (ρ j)) : A/B ≤ y :=
    (div_le_div_of_nonneg_left hA.le (hq j) (hfreq j)).trans
      (spectralFrequencyTestProfile_support_lower (q j) (hq j) F hFB hy)
  exact ⟨fun j => spectralFrequencyTestProfile_contDiff (q j) F hF hFp,
    fun j => spectralFrequencyTestProfile_compact (q j) (hq j) F hcF,
    fun j _ hy => (div_pos hA hB).trans_le (hlo j hy),
    fun j _ hy => hYB.trans_le (hlo j hy)⟩

theorem gamma0Infinity_common_physical_packet_norm_le {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n)
    (hn₀ : ∀ j, n j ≠ 0) (F : ℝ → ℝ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hFB : tsupport F ⊆ Ici A)
    (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
    (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hProfile : ∀ j, ρ j = spectralFrequencyTestProfile |cuspFourierFrequency 1 (n j)| F) :
    let nN (j : ι) := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
    ‖gamma0FourierPoincarePacket N u α (fun _ => 1) nN ρ hρ hcρ hpρ‖^2 ≤
      (2*(N : ℝ))^2*(6*(1+2*B/((N : ℝ)*A))*
        ((∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ j ∈ u, ‖α j‖^2))) := by
  let nN (j : ι) := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let q (j : ι) := |cuspFourierFrequency 1 (n j)|
  let P := gamma0FourierPoincarePacket N u α (fun _ => 1) nN ρ hρ hcρ hpρ
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let S := ∑ j ∈ u, ‖α j‖^2
  let V := 6*(1+2*B/((N : ℝ)*A))
  have hq (j : ι) : 0 < q j :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos (n j) (hn₀ j))
  have hlo (j : ι) {y : ℝ} (hy : y ∈ tsupport (ρ j)) : A/B ≤ y := by
    rw [hProfile j] at hy
    exact (div_le_div_of_nonneg_left hA.le (hq j) (hfreq j)).trans
      (spectralFrequencyTestProfile_support_lower (q j) (hq j) F hFB hy)
  have hMass (j : ι) : cuspFourierHeightPairing (ρ j) (ρ j) = M := by
    rw [hProfile j]
    exact spectralFrequencyTestProfile_height_mass (q j) (hq j) F
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hN₁ : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos N)
  have hnN : Function.Injective nN := by
    intro j k h
    apply hn
    exact mul_left_cancel₀ (show (gamma0CuspFrequencyStep N 1 : ℤ) ≠ 0 by
      exact_mod_cast (gamma0CuspFrequencyStep_pos N 1).ne') h
  have h := gamma0InfinityFourierPoincarePacket_orbit_normsq_le N u α nN hnN
    ρ hρ hcρ hpρ (div_pos hA hB) (fun j _ _ hy => hlo j hy)
  change ‖P‖^2 ≤ _ at h
  simp only [hMass,← Finset.sum_mul] at h
  have hC : 2*((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*(A/B)))))*(N : ℝ) ≤
      (2*(N : ℝ))^2*V := by
    have hr : 2/((N : ℝ)*(A/B)) = 2*B/((N : ℝ)*A) := by
      field_simp [hN.ne',hA.ne',hB.ne']
    calc
      _ ≤ 2*((3*(N : ℝ))*(4*(1+2/((N : ℝ)*(A/B)))))*(N : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith only [hN₁]) (by positivity)) (by norm_num)) hN.le
      _ = _ := by rw [hr]; dsimp only [V]; ring
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change ‖P‖^2 ≤ (2*(N : ℝ))^2*(V*(M*S))
  calc
    _ ≤ _ := h
    _ = (2*((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*(A/B)))))*(N : ℝ))*(M*S) := by
      dsimp only [S]
      ring
    _ ≤ ((2*(N : ℝ))^2*V)*(M*S) := mul_le_mul_of_nonneg_right hC (mul_nonneg hM hS)
    _ = _ := mul_assoc _ _ _

end ArtinMatthews
