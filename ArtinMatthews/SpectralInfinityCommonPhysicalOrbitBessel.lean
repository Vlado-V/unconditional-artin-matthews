module

public import ArtinMatthews.SpectralTrueWidthBesselPairing
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspWidthNormalization
public import ArtinMatthews.SpectralCuspWidthRefinement
public import ArtinMatthews.SpectralFrequencyTestProfile
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine common physical Bessel test at all positive heights.
The orbit count supplies the explicit additional frequency factor. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0Infinity_common_physical_test_orbit_bessel {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ι)
    (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (hn0 : ∀ j, n j ≠ 0)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hYB : Y < A/B)
    (hFB : tsupport F ⊆ Ici A) (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
    let Fhat (i : Gamma0AllHeightSpectralIndex N) := ∫ x : ℝ, (F x : ℂ)*
      schlafliBesselK (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))) x
      ∂spectralKLPhysicalMeasure
    (∑ i ∈ u, ‖Fhat i*(∑ j ∈ t, star (α j)*
      gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)))‖^2) ≤
      6*(1+2*B/((N : ℝ)*A))*
        ((∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ j ∈ t, ‖α j‖^2)) := by
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let q j := |cuspFourierFrequency 1 (n j)|
  let ρ j := spectralFrequencyTestProfile (q j) F
  have hq (j : ι) : 0 < q j := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos (n j) (hn0 j))
  have hFp : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hFB hx)
  have hρ (j : ι) : ContDiff ℝ ∞ (ρ j) := spectralFrequencyTestProfile_contDiff (q j) F hF hFp
  have hcρ (j : ι) : HasCompactSupport (ρ j) := spectralFrequencyTestProfile_compact (q j) (hq j) F hcF
  have hlo (j : ι) (y : ℝ) (hy : y ∈ tsupport (ρ j)) : A/B ≤ y := by
    exact (div_le_div_of_nonneg_left hA.le (hq j) (hfreq j)).trans
      (spectralFrequencyTestProfile_support_lower (q j) (hq j) F hFB hy)
  have hpρ (j : ι) : tsupport (ρ j) ⊆ Ioi (0 : ℝ) :=
    fun y hy => (div_pos hA hB).trans_le (hlo j y hy)
  have hsρ (j : ι) : tsupport (ρ j) ⊆ Ioi Y := fun y hy => hYB.trans_le (hlo j y hy)
  let P := gamma0FourierPoincarePacket N t α (fun _ => 1) nN ρ hρ hcρ hpρ
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let ν (i : Gamma0AllHeightSpectralIndex N) := Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))
  let Fhat (i : Gamma0AllHeightSpectralIndex N) := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (ν i) x
    ∂spectralKLPhysicalMeasure
  let C (i : Gamma0AllHeightSpectralIndex N) (j : ι) :=
    gamma0CuspBesselAmplitude N i 1 Y hY (nN j) (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))
  have hMass (j : ι) : cuspFourierHeightPairing (ρ j) (ρ j) = M :=
    spectralFrequencyTestProfile_height_mass (q j) (hq j) F
  let S := ∑ j ∈ t, ‖α j‖^2
  let V := 6*(1+2*B/((N : ℝ)*A))
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hN₁ : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos N)
  have hAraw : 0 < A/B := div_pos hA hB
  have hnN : Function.Injective nN := by
    intro j k h
    apply hn
    exact mul_left_cancel₀ (show (gamma0CuspFrequencyStep N 1 : ℤ) ≠ 0 by
      exact_mod_cast (gamma0CuspFrequencyStep_pos N 1).ne') h
  have hP : ‖P‖^2 ≤ (2*(N : ℝ))^2*(V*(M*S)) := by
    have h := gamma0InfinityFourierPoincarePacket_orbit_normsq_le N t α nN hnN
      ρ hρ hcρ hpρ hAraw (fun j _ => hlo j)
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
    calc
      _ ≤ _ := h
      _ = (2*((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*(A/B)))))*(N : ℝ))*(M*S) := by
        dsimp only [S]
        ring
      _ ≤ ((2*(N : ℝ))^2*V)*(M*S) := mul_le_mul_of_nonneg_right hC (mul_nonneg hM hS)
      _ = _ := mul_assoc _ _ _
  have hqN (j : ι) : |cuspFourierFrequency (N : ℝ) (nN j)| = q j := by
    simpa only [nN,q,gamma0CuspTrueWidth_identity,Nat.cast_one,mul_one] using
      cuspFourierFrequency_abs_trueWidth N 1 (n j)
  have hCoeff (i : Gamma0AllHeightSpectralIndex N) (j : ι) :
      gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) (ρ j) =
        (2*(N : ℂ))*C i j*Fhat i := by
    rw [gamma0FourierPoincareSpectralCoefficient,hqN,
      spectralFrequencyTestProfile_transform (q j) (hq j) F (ν i) Y hY.le (hsρ j)]
  have hrow (i : Gamma0AllHeightSpectralIndex N) :
      (∑ j ∈ t, star (α j)*gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) (ρ j)) =
        (2*(N : ℂ))*(Fhat i*(∑ j ∈ t, star (α j)*C i j)) := by
    simp only [hCoeff,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnorm (z : ℂ) : ‖(2*(N : ℂ))*z‖^2 = (2*(N : ℝ))^2*‖z‖^2 := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,show ‖(2 : ℂ)‖ = (2 : ℝ) from Complex.norm_natCast 2]
    exact mul_pow _ _ _
  have hBessel := gamma0FourierPoincarePacket_finite_bessel N u t α (fun _ => 1) nN
    (fun j => gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) Y hY
    ρ hρ hcρ hpρ hsρ
  simp only [hrow,hnorm] at hBessel
  change (∑ i ∈ u, ‖Fhat i*(∑ j ∈ t, star (α j)*C i j)‖^2) ≤ V*(M*S)
  apply (mul_le_mul_iff_of_pos_left (show 0 < (2*(N : ℝ))^2 by positivity)).mp
  calc
    _ ≤ ‖P‖^2 := by rw [Finset.mul_sum]; exact hBessel
    _ ≤ _ := hP

end ArtinMatthews
