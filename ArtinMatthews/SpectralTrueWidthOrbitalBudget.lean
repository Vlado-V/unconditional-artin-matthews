module

public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import ArtinMatthews.SpectralKLCuspWidthTransform
public import ArtinMatthews.SpectralOrbitalWidthBudget
public import ArtinMatthews.SpectralWeylCompactNormBound
public import ArtinMatthews.SpectralWeylTwoHeightKernel
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

/-! The actual compact true-width Bessel orbital norm is bounded in
terms of the original heights and the integral lower entry. The two
true widths cancel exactly inside this bound, while the period
multiplicities outside the orbital integral are retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0TrueWidthBesselOrbital_height_bound (N q : ℕ) [NeZero N] [NeZero q]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hM : ∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) :
    ‖gamma0TrueWidthBesselOrbital N r s q m n ρ η‖ ≤
      spectralWeylCompactHeightBudget A B M ρ/(q : ℝ)^3 := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let v : ℝ := gamma0CuspTrueWidth N s
  let C := gamma0TrueWidthModulus N r s (q : ℝ)
  let R : ℝ → ℝ := fun y => ρ (w*y)
  let E : ℝ → ℝ := fun z => η (v*z)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hv : 0 < v := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s hq
  obtain ⟨hR,hRc,hRp⟩ := spectral_cusp_width_test_properties w 0 hw ρ hρ.continuous hcρ hpρ
  obtain ⟨hE,hEc,hEp⟩ := spectral_cusp_width_test_properties v 0 hv η hη.continuous hcη hpη
  have hRp' : tsupport R ⊆ Ioi (0 : ℝ) := by simpa only [R,zero_div] using hRp
  have hEp' : tsupport E ⊆ Ioi (0 : ℝ) := by simpa only [E,zero_div] using hEp
  have hRlo (y : ℝ) (hy : y ∈ tsupport R) : A/w ≤ y := by
    have hy' : w*y ∈ tsupport ρ := tsupport_comp_subset_preimage
      (f := fun x : ℝ => w*x) ρ (by fun_prop) hy
    exact (div_le_iff₀ hw).mpr (by simpa only [mul_comm] using hρlo (w*y) hy')
  have hElo (z : ℝ) (hz : z ∈ tsupport E) : B/v ≤ z := by
    have hz' : v*z ∈ tsupport η := tsupport_comp_subset_preimage
      (f := fun x : ℝ => v*x) η (by fun_prop) hz
    exact (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hηlo (v*z) hz')
  have hME (z : ℝ) : ‖spectralKLHeightBaseTest E z‖ ≤ Real.sqrt v*M := by
    rw [spectralKLHeightBaseTest_width_norm v hv]
    exact mul_le_mul_of_nonneg_left (hM (v*z)) (Real.sqrt_nonneg v)
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hI : Integrable (cuspWeylOrbitalIntegrand 1 m n R E C hC.ne') := by
    simpa only [R,E,C,w,v,Int.cast_natCast] using!
      cuspWeylOrbitalIntegrand_trueWidth_integrable N r s m n ρ η hρ hη hcρ hcη hpρ hpη (q : ℤ) hqz
  have he : cuspWeylOrbitalKernel 1 m n R E C hC.ne' = gamma0TrueWidthBesselOrbital N r s q m n ρ η :=
    gamma0TrueWidthOrbitalKernel_nonzero_bessel N r s q m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
  rw [← he]
  refine (cuspWeylOrbitalKernel_compact_norm_bound 1 m n R E hR hRc hRp' hE hEc hEp'
    (div_pos hA hw) (div_pos hB hv) hC hRlo hElo hME
    (weylPlanarDensity_integrable_of_orbital 1 m n R E C hC.ne' hI)).trans_eq ?_
  calc
    _ = spectralWeylCompactHeightBudget (A/w) (B/v) (Real.sqrt v*M) R/C^3 := by
      unfold spectralWeylCompactHeightBudget
      field_simp [hC.ne',hw.ne',hv.ne',hA.ne',hB.ne']
    _ = _ := by
      rw [spectralWeylCompactHeightBudget_width hw hv hA hB M ρ]
      have hce : C = (q : ℝ)*(Real.sqrt w*Real.sqrt v) := by
        change (q : ℝ)*Real.sqrt w*Real.sqrt v = _
        exact mul_assoc _ _ _
      rw [hce,mul_pow]
      field_simp [hq.ne',(Real.sqrt_pos.mpr hw).ne',(Real.sqrt_pos.mpr hv).ne']

theorem gamma0TrueWidthBesselGeometricFibre_height_bound (N q : ℕ) [NeZero N] [NeZero q]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hM : ∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) :
    ‖gamma0TrueWidthBesselGeometricFibre N r s q m n ρ η‖ ≤
      ((gamma0CuspFrequencyStep N s : ℝ)*(gamma0CuspFrequencyStep N r : ℝ))*
        ‖gamma0TrueWidthKloostermanSum N r s q m n‖*
          (spectralWeylCompactHeightBudget A B M ρ/(q : ℝ)^3) := by
  have h := gamma0TrueWidthBesselOrbital_height_bound N q r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
    hA hB hρlo hηlo hM
  simp only [gamma0TrueWidthBesselGeometricFibre,norm_mul,Complex.norm_natCast,← mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end ArtinMatthews
