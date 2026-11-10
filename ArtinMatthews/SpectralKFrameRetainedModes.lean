module

public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralKFrameLogWindow
public import ArtinMatthews.SpectralFiniteFourierFrame
public import ArtinMatthews.SpectralKFrameLogDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! A linear number of ordinary Fourier modes retains a fixed
fraction of the actual logarithmic K square mass on each dyadic band. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace ArtinMatthews

theorem spectralKFrameLogTest_retained_mass (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384))
    (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1)
    (hOne : ∀ u ∈ Icc (Real.log 4) (Real.log 192), ψ u = 1)
    {D : ℝ} (hDψ : ∀ u, |deriv ψ u| ≤ D)
    (T t : ℝ) (hT : 0 < T) (ht₁ : T ≤ 1+|t|) (ht₂ : 1+|t| ≤ 2*T)
    (s : Finset ℤ) {b : ℝ} (hb : 0 < b)
    (hcut : ∀ n : ℤ, n ∉ s → b ≤ |cuspFourierFrequency spectralKFrameLength n|)
    (hbsq : 1296*(32*(4*D^2+15/2))*T^2 ≤ b^2) :
    spectralKSquareMoment 0 t/(1296*spectralKFrameLength*T) ≤
      ∑ n ∈ s, ‖fourierCoeffOn spectralKFrameLength_pos
        (fun u => (spectralKFrameLogTest ψ T t u : ℂ)) n‖^2 := by
  let L := spectralKFrameLength
  let I := spectralKSquareMoment 0 t
  let C := 32*(4*D^2+15/2)
  let G := spectralKFrameLogTest ψ T t
  let f : ℝ → ℂ := fun u => (G u : ℂ)
  have hL : 0 < L := spectralKFrameLength_pos
  have hI : 0 ≤ I := by
    change 0 ≤ spectralKSquareMoment 0 t
    rw [spectralKSquareMoment_zero]
    positivity
  have hG : ContDiff ℝ 1 G := spectralKFrameLogTest_contDiff_one ψ hψ T t hT
  have hf : ContDiff ℝ 1 f := Complex.ofRealCLM.contDiff.comp hG
  have hfd (u : ℝ) : deriv f u = ((deriv G u : ℝ) : ℂ) :=
    ((hG.differentiable (by simp) u).hasDerivAt.ofReal_comp).deriv
  have hE := spectralKFrameLogTest_endpoints ψ hSupp T t
  have he : f L = f 0 := by dsimp only [f,G,L]; rw [hE.1,hE.2]
  have h := spectral_fourierCoeffOn_energy_truncation hL f hf he s hb hcut
  simp only [hfd,f,Complex.norm_real,Real.norm_eq_abs,sq_abs] at h
  have hM : I/(648*T) ≤ ∫ u in (0 : ℝ)..L, (G u)^2 :=
    spectralKFrameLogTest_mass_lower ψ hψ hOne T t hT ht₁ ht₂
  have hE' : (∫ u in (0 : ℝ)..L, (deriv G u)^2) ≤ C*T*I :=
    spectralKFrameLogTest_deriv_energy ψ hψ hSupp h01 hDψ T t hT ht₂
  have htail :
      (b^2)⁻¹*(L⁻¹*(∫ u in (0 : ℝ)..L, (deriv G u)^2)) ≤ I/(1296*L*T) := by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE' (inv_nonneg.mpr hL.le))
      (inv_nonneg.mpr (sq_nonneg _))).trans ?_
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    calc
      _ = I/(1296*L*T)*(1296*C*T^2) := by field_simp [hT.ne',hL.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hbsq (by positivity)
  have hmass' : 2*(I/(1296*L*T)) ≤ L⁻¹*(∫ u in (0 : ℝ)..L, (G u)^2) := by
    calc
      _ = L⁻¹*(I/(648*T)) := by field_simp [hT.ne',hL.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hL.le)
  change I/(1296*L*T) ≤ ∑ n ∈ s, ‖fourierCoeffOn hL f n‖^2
  linarith only [hmass',h,htail]

theorem spectralKFrameLogTest_exists_retained_modes (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384))
    (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1)
    (hOne : ∀ u ∈ Icc (Real.log 4) (Real.log 192), ψ u = 1)
    {D : ℝ} (hDψ : ∀ u, |deriv ψ u| ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, (1/2 : ℝ) ≤ T →
      ∃ s : Finset ℤ, (s.card : ℝ) ≤ C*T ∧
        ∀ t : ℝ, T ≤ 1+|t| → 1+|t| ≤ 2*T →
          spectralKSquareMoment 0 t/(1296*spectralKFrameLength*T) ≤
            ∑ n ∈ s, ‖fourierCoeffOn spectralKFrameLength_pos
              (fun u => (spectralKFrameLogTest ψ T t u : ℂ)) n‖^2 := by
  let L := spectralKFrameLength
  let A := 1296*(32*(4*D^2+15/2))
  let B := 1+A
  have hL : 0 < L := spectralKFrameLength_pos
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBsq : A ≤ B^2 := by dsimp only [B]; nlinarith [sq_nonneg A]
  refine ⟨B*L/Real.pi+6,by positivity,?_⟩
  intro T hhalf
  have hT : 0 < T := by linarith
  let W := B*T*L/(2*Real.pi)
  let m : ℤ := ⌈W⌉
  let s := Finset.Icc (-m) m
  have hW : 0 < W := by dsimp only [W]; positivity
  have hceil : W ≤ (m : ℝ) := Int.le_ceil W
  have hm : 0 ≤ m := by exact_mod_cast (hW.le.trans hceil)
  have hupper : (m : ℝ) < W+1 := Int.ceil_lt_add_one W
  refine ⟨s,?_,?_⟩
  · have hsInt : (s.card : ℤ) = m+1-(-m) :=
      Int.card_Icc_of_le (-m) m (by omega)
    have hs : (s.card : ℝ) = 2*(m : ℝ)+1 := by
      exact_mod_cast (by omega : (s.card : ℤ) = 2*m+1)
    rw [hs]
    have hWscale : 2*W = (B*L/Real.pi)*T := by dsimp only [W]; ring
    nlinarith only [hWscale,hupper,hhalf]
  · intro t ht₁ ht₂
    apply spectralKFrameLogTest_retained_mass ψ hψ hSupp h01 hOne hDψ T t hT ht₁ ht₂
      s (b := B*T) (by positivity)
    · intro n hn
      have hmn : m ≤ |n| := by
        by_contra! h'
        exact hn (Finset.mem_Icc.mpr ⟨(abs_lt.mp h').1.le,(abs_lt.mp h').2.le⟩)
      have hcast : (m : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hmn
      have hfreq : |cuspFourierFrequency L n| = (2*Real.pi)*|(n : ℝ)|/L := by
        rw [cuspFourierFrequency,abs_div,abs_mul,abs_of_pos hL,
          abs_of_pos (show 0 < 2*Real.pi by positivity)]
      rw [hfreq]
      apply (le_div_iff₀ hL).mpr
      have hw := (div_le_iff₀ (show 0 < 2*Real.pi by positivity)).mp (hceil.trans hcast)
      simpa only [mul_comm (|(n : ℝ)|)] using hw
    · rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hBsq (sq_nonneg _)

end ArtinMatthews
