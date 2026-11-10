module

public import ArtinMatthews.SpectralFrequencyTestProfile
public import ArtinMatthews.SpectralKFrameCompactProfiles
public import ArtinMatthews.SpectralEisensteinAnalysisCompletion
public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralNativeCompactContinuous
public import ArtinMatthews.SpectralNativeOrderTransform
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

/-! The actual continuous coefficient of an infinity Fourier packet
has a common compact K transform at all of its primitive frequencies. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

def gamma0InfinityContinuousPacketFourier {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (i : Gamma0EisensteinCuspClasses N) (t : ℝ) : ℂ :=
  ∑ j ∈ u, star (α j)*gamma0PrimitiveFourierAmplitude N
    (gamma0EisensteinCuspClassRepresentative N i) 1 Y hY (n j) (hn j) (eisensteinCriticalPoint t)

theorem gamma0Infinity_analysis_compact_profile_ae (N : ℕ) [NeZero N]
    (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y) (F ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y)
    (hProfile : ρ = spectralFrequencyTestProfile |cuspFourierFrequency 1 n| F)
    (i : Gamma0EisensteinCuspClasses N) :
    (gamma0EisensteinAnalysis N (gamma0PrimitiveFourierPoincareTest N 1 n ρ hρ hcρ hpρ)) i
      =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star
        (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i)
          1 Y hY n hn (eisensteinCriticalPoint t)*spectralCompactRealKTransform F t) := by
  let q := |cuspFourierFrequency 1 n|
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hs : tsupport (spectralFrequencyTestProfile q F) ⊆ Ioi Y := hProfile ▸ hsρ
  filter_upwards [gamma0PrimitiveAnalysis_fourier_ae N 1 n hn Y hY Y hY ρ hρ hcρ hpρ hsρ i]
    with t ht
  rw [ht]
  simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul]
  rw [← cuspBesselTransform_eq_order_integral _ hq hY ρ hsρ,
    hProfile,spectralFrequencyTestProfile_transform q hq F _ Y hY.le hs]
  rfl

theorem gamma0Infinity_analysis_compact_packet_ae {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (F : ℝ → ℝ) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) (hsρ : ∀ j, tsupport (ρ j) ⊆ Ioi Y)
    (hProfile : ∀ j, ρ j = spectralFrequencyTestProfile |cuspFourierFrequency 1 (n j)| F)
    (i : Gamma0EisensteinCuspClasses N) :
    let U := ∑ j ∈ u, α j • gamma0PrimitiveFourierPoincareTest N 1 (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)
    (gamma0EisensteinAnalysis N U) i =ᵐ[gamma0EisensteinSpectralMeasure] fun t =>
      star (spectralCompactRealKTransform F t*gamma0InfinityContinuousPacketFourier N u α n hn Y hY i t) := by
  let L : Gamma0RegionL2 N →L[ℂ] Lp ℂ 2 gamma0EisensteinSpectralMeasure :=
    (PiLp.proj 2 _ i).comp (gamma0EisensteinAnalysis N)
  let U (j : ι) := gamma0PrimitiveFourierPoincareTest N 1 (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)
  let K := spectralCompactRealKTransform F
  let A (j : ι) (t : ℝ) := gamma0PrimitiveFourierAmplitude N
    (gamma0EisensteinCuspClassRepresentative N i) 1 Y hY (n j) (hn j) (eisensteinCriticalPoint t)
  have hAE (j : ι) : L (U j) =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star (A j t*K t) :=
    gamma0Infinity_analysis_compact_profile_ae N (n j) (hn j) Y hY F (ρ j)
      (hρ j) (hcρ j) (hpρ j) (hsρ j) (hProfile j) i
  have hSum (j : ι) : ⇑(α j • L (U j)) =ᵐ[gamma0EisensteinSpectralMeasure]
      fun t => α j*star (A j t*K t) := by
    filter_upwards [Lp.coeFn_smul (α j) (L (U j)),hAE j] with t hs ht
    change _ = α j*star (A j t*K t)
    rw [hs]
    change α j*L (U j) t = _
    rw [ht]
  change ⇑(L (∑ j ∈ u, α j • U j)) =ᵐ[gamma0EisensteinSpectralMeasure] _
  simp only [map_sum,map_smul]
  refine (Lp.coeFn_fun_finsetSum u (fun j => α j • L (U j))).trans ?_
  filter_upwards [eventuallyEq_sum (s := u) (fun j _ => hSum j)] with t ht
  simp only [Finset.sum_apply] at ht
  rw [ht]
  change (∑ j ∈ u, α j*star (A j t*K t)) =
    (starRingEnd ℂ) (K t*(∑ j ∈ u, (starRingEnd ℂ) (α j)*A j t))
  rw [map_mul,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change α j*(starRingEnd ℂ) (A j t*K t) =
    (starRingEnd ℂ) (K t)*(starRingEnd ℂ) ((starRingEnd ℂ) (α j)*A j t)
  rw [map_mul,map_mul,show (starRingEnd ℂ) ((starRingEnd ℂ) (α j)) = α j from star_star _]
  ring

end ArtinMatthews
