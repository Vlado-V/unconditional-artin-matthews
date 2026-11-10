module

public import ArtinMatthews.SpectralHeatSpectralPairing
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspWidthNormalization
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralInfinityPhysicalPacketMass
public import ArtinMatthews.SpectralResidualBasisBessel
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

/-! The actual finite residual coefficients of an infinity packet share
the same compact physical transform, with literal source normalization. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators
namespace ArtinMatthews

def gamma0InfinityResidualPacketRho {ι : Type*} (N : ℕ) [NeZero N]
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ k, n k ≠ 0) : ℂ :=
  ∑ k ∈ u, star (α k)*((Real.sqrt |(n k : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j 1 (n k) (hn k))

theorem gamma0ResidualABLSourceRho_infinity_scale (N : ℕ) [NeZero N]
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (n : ℤ) (hn : n ≠ 0) :
    (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j 1 n hn =
      gamma0AmbientBesselAmplitude N l l.property (gamma0ResidualEigenbasis N l j).val
        (gamma0ResidualEigenbasis_green N l j) 1 ((gamma0CuspFrequencyStep N 1 : ℤ)*n)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 hn) := by
  unfold gamma0ResidualABLSourceRho gamma0AmbientABLSourceRho
  rw [spectralABLRhoFromNative_scale _ _ (abs_pos.mpr (by exact_mod_cast hn)),
    gamma0CuspTrueWidth_identity,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,one_mul]

theorem gamma0Infinity_residual_physical_packet_bound {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n)
    (hn₀ : ∀ k, n k ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hYB : Y < A/B)
    (hFB : tsupport F ⊆ Ici A) (hfreq : ∀ k, |cuspFourierFrequency 1 (n k)| ≤ B) :
    let K (l : Ici (0 : ℝ)) :=
      ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (Complex.sqrt (1/4-((l : ℝ) : ℂ))) x ∂spectralKLPhysicalMeasure
    (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖K l*gamma0InfinityResidualPacketRho N l j u α n hn₀‖^2) ≤
      6*(1+2*B/((N : ℝ)*A))*
        ((∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ k ∈ u, ‖α k‖^2))/4 := by
  let q (k : ι) := |cuspFourierFrequency 1 (n k)|
  let ρ (k : ι) := spectralFrequencyTestProfile (q k) F
  let nN (k : ι) := (gamma0CuspFrequencyStep N 1 : ℤ)*n k
  obtain ⟨hρ,hcρ,hpρ,hsρ⟩ :=
    spectralCommonFrequencyProfile_properties n hn₀ F hF hcF hA hB hFB hfreq hYB
  let P := gamma0FourierPoincarePacket N u α (fun _ => 1) nN ρ hρ hcρ hpρ
  let K (l : Ici (0 : ℝ)) :=
    ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (Complex.sqrt (1/4-((l : ℝ) : ℂ))) x ∂spectralKLPhysicalMeasure
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let S := ∑ k ∈ u, ‖α k‖^2
  let V := 6*(1+2*B/((N : ℝ)*A))
  have hq (k : ι) : 0 < q k := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos (n k) (hn₀ k))
  have hqN (k : ι) : |cuspFourierFrequency (N : ℝ) (nN k)| = q k := by
    simpa only [nN,q,gamma0CuspTrueWidth_identity,Nat.cast_one,mul_one] using
      cuspFourierFrequency_abs_trueWidth N 1 (n k)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hP : ‖P‖^2 ≤ (2*(N : ℝ))^2*(V*(M*S)) :=
    gamma0Infinity_common_physical_packet_norm_le N u α n hn hn₀ F hA hB hFB hfreq ρ hρ hcρ hpρ
      (fun _ => rfl)
  have hPair (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
      inner ℂ P (gamma0ResidualEigenbasis N l j).val =
        (4*(N : ℂ))*(K l*gamma0InfinityResidualPacketRho N l j u α n hn₀) := by
    unfold P gamma0FourierPoincarePacket gamma0InfinityResidualPacketRho
    simp only [sum_inner,inner_smul_left,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hp := gamma0FourierPoincareTest_ambient_inner N l l.property (gamma0ResidualEigenbasis N l j).val
      (gamma0ResidualEigenbasis_green N l j) 1 (nN k)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn₀ k)) Y hY (ρ k) (hρ k) (hcρ k) (hpρ k) (hsρ k)
    rw [hqN,spectralFrequencyTestProfile_transform (q k) (hq k) F _ Y hY.le (hsρ k),
      ← gamma0ResidualABLSourceRho_infinity_scale N l j (n k) (hn₀ k)] at hp
    rw [hp]
    change (starRingEnd ℂ) (α k)*((2*(N : ℂ))*_ * K l) =
      (4*(N : ℂ))*(K l*((starRingEnd ℂ) (α k)*_))
    ring
  have hScale (z : ℂ) : ‖(4*(N : ℂ))*z‖^2 = (4*(N : ℝ))^2*‖z‖^2 := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,show ‖(4 : ℂ)‖ = (4 : ℝ) from Complex.norm_natCast 4]
    exact mul_pow _ _ _
  have hBessel := gamma0ResidualEigenbasis_pairing_sq_sum_le N P
  simp only [hPair,hScale,← Finset.mul_sum] at hBessel
  change (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖K l*gamma0InfinityResidualPacketRho N l j u α n hn₀‖^2)
    ≤ V*(M*S)/4
  apply (mul_le_mul_iff_of_pos_left (show 0 < (4*(N : ℝ))^2 by positivity)).mp
  exact (hBessel.trans hP).trans_eq (by ring)

end ArtinMatthews
