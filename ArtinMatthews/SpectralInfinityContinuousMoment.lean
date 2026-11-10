module

public import ArtinMatthews.SpectralInfinityContinuousPacket
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralInfinityPhysicalPacketMass
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

/-! The continuous compact packet satisfies the genuine infinity orbit
bound with its exact primitive normalization. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators
namespace ArtinMatthews

theorem gamma0Infinity_primitive_physical_packet_norm_le {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n)
    (hn₀ : ∀ j, n j ≠ 0) (F : ℝ → ℝ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hFB : tsupport F ⊆ Ici A)
    (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
    (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hProfile : ∀ j, ρ j = spectralFrequencyTestProfile |cuspFourierFrequency 1 (n j)| F) :
    ‖∑ j ∈ u, α j • gamma0PrimitiveFourierPoincareTest N 1 (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)‖^2 ≤
      6*(1+2*B/((N : ℝ)*A))*
        ((∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ j ∈ u, ‖α j‖^2)) := by
  let nN (j : ι) := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let P := gamma0FourierPoincarePacket N u α (fun _ => 1) nN ρ hρ hcρ hpρ
  let c := gamma0PrimitiveFourierScale N 1
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hC : ‖c‖ = (2*(N : ℝ))⁻¹ := by
    dsimp only [c,gamma0PrimitiveFourierScale]
    rw [gamma0CuspTrueWidth_identity,Nat.cast_one,Complex.norm_real,
      Real.norm_of_nonneg (by positivity),one_div]
  have hP := gamma0Infinity_common_physical_packet_norm_le N u α n hn hn₀ F
    hA hB hFB hfreq ρ hρ hcρ hpρ hProfile
  have hEq : (∑ j ∈ u, α j • gamma0PrimitiveFourierPoincareTest N 1 (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)) =
      c • P := by
    unfold P gamma0FourierPoincarePacket
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [gamma0PrimitiveFourierPoincareTest_eq,smul_smul,smul_smul,mul_comm (α j)]
  rw [hEq,norm_smul,hC,mul_pow]
  refine (mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq ?_
  rw [← mul_assoc,← mul_pow,inv_mul_cancel₀ (by positivity : (2*(N : ℝ)) ≠ 0),one_pow,one_mul]

theorem gamma0Infinity_physical_continuous_moment {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n)
    (hn₀ : ∀ j, n j ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hYB : Y < A/B)
    (hFB : tsupport F ⊆ Ici A) (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) :
    let K := spectralCompactRealKTransform F
    let W := gamma0InfinityContinuousPacketFourier N u α n hn₀ Y hY
    let C (t : ℝ) := ∑ i : Gamma0EisensteinCuspClasses N, ‖K t*W i t‖^2
    Integrable C gamma0EisensteinSpectralMeasure ∧
      (∫ t, C t ∂gamma0EisensteinSpectralMeasure) ≤
        6*(1+2*B/((N : ℝ)*A))*
          ((∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ j ∈ u, ‖α j‖^2)) := by
  let ρ (j : ι) := spectralFrequencyTestProfile |cuspFourierFrequency 1 (n j)| F
  obtain ⟨hρ,hcρ,hpρ,hsρ⟩ :=
    spectralCommonFrequencyProfile_properties n hn₀ F hF hcF hA hB hFB hfreq hYB
  let U := ∑ j ∈ u, α j • gamma0PrimitiveFourierPoincareTest N 1 (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)
  let V := gamma0EisensteinAnalysis N U
  let K := spectralCompactRealKTransform F
  let W := gamma0InfinityContinuousPacketFourier N u α n hn₀ Y hY
  let μ := gamma0EisensteinSpectralMeasure
  have hRow (i : Gamma0EisensteinCuspClasses N) :
      (fun t => ‖K t*W i t‖^2) =ᵐ[μ] fun t => ‖V i t‖^2 := by
    have h := gamma0Infinity_analysis_compact_packet_ae N u α n hn₀ Y hY F ρ
      hρ hcρ hpρ hsρ (fun _ => rfl) i
    filter_upwards [h] with t ht
    change V i t = star (K t*W i t) at ht
    rw [ht,norm_star]
  have hI (i : Gamma0EisensteinCuspClasses N) : Integrable (fun t => ‖K t*W i t‖^2) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (V i))).mp (Lp.memLp (V i))
    exact hi.congr (hRow i).symm
  have hEq (i : Gamma0EisensteinCuspClasses N) : (∫ t, ‖V i t‖^2 ∂μ) = ‖V i‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    rfl
  change Integrable (fun t => ∑ i, ‖K t*W i t‖^2) μ ∧ _
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hI i),?_⟩
  have hMass : (∫ t, ∑ i, ‖K t*W i t‖^2 ∂μ) = ‖V‖^2 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hI i),PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_congr_ae (hRow i),hEq]
  rw [hMass]
  exact (pow_le_pow_left₀ (norm_nonneg _) (gamma0EisensteinAnalysis_norm_le N U) 2).trans
    (gamma0Infinity_primitive_physical_packet_norm_le N u α n hn hn₀ F
      hA hB hFB hfreq ρ hρ hcρ hpρ (fun _ => rfl))

end ArtinMatthews
