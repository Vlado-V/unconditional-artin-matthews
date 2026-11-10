module

public import ArtinMatthews.SpectralWeylPlanarCoordinates
public import ArtinMatthews.AtkinLehnerMixedWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Direct absolute integration of the actual Weyl orbital on two
comparable compact height supports. The bound is uniform as the
common height scale tends to zero. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem cuspWeylOrbitalKernel_comparable_height_norm_le
    (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ) {a c M₁ M₂ : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hρ : Function.support ρ ⊆ Icc a (2*a)) (hη : Function.support η ⊆ Icc a (2*a))
    (hρM : ∀ y ∈ Icc a (2*a), ‖ρ y‖ ≤ Real.sqrt y*M₁)
    (hηM : ∀ y ∈ Icc a (2*a), ‖η y‖ ≤ Real.sqrt y*M₂)
    (hi : IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ×ℝ | 0 < p.2}) :
    ‖cuspWeylOrbitalKernel N m n ρ η c hc.ne'‖ ≤ 8*M₁*M₂/c := by
  let U : Set (ℝ×ℝ) := {p | 0 < p.2}
  let Q : Set (ℝ×ℝ) := Icc (-(2/c)) (2/c) ×ˢ Icc a (2*a)
  let D := weylPlanarDensity N m n ρ η c
  let V (p : ℝ×ℝ) := p.2/(c^2*(p.1^2+p.2^2))
  have hQU : Q ⊆ U := fun _ hp => ha.trans_le hp.2.1
  have hUc : MeasurableSet U := measurableSet_lt measurable_const measurable_snd
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hplace (p : ℝ×ℝ) (hp : p ∈ U) (hne : D p ≠ 0) :
      p ∈ Q ∧ V p ∈ Icc a (2*a) := by
    have hρn : ρ p.2 ≠ 0 := by
      intro he
      apply hne
      simp only [D,weylPlanarDensity,weylPlanarIntegrand,weylPlanarAmplitude,he,zero_mul,
        Complex.ofReal_zero,smul_zero]
    have hηn : η (V p) ≠ 0 := by
      intro he
      apply hne
      change (p.2^2)⁻¹ • (((ρ p.2*η (V p) : ℝ) : ℂ)*atkinPhase (weylPlanarPhase N m n c p.1 p.2)) = 0
      rw [he,mul_zero,Complex.ofReal_zero,zero_mul,smul_zero]
    have hy := hρ hρn
    have hv := hη hηn
    have hden : 0 < c^2*(p.1^2+p.2^2) := mul_pos (sq_pos_of_pos hc)
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hp))
    have hV : a*(c^2*(p.1^2+p.2^2)) ≤ p.2 := (le_div_iff₀ hden).mp hv.1
    have hx : (c*p.1)^2 ≤ 2 := by
      apply (mul_le_mul_iff_of_pos_left ha).mp
      calc
        a*(c*p.1)^2 ≤ a*(c^2*(p.1^2+p.2^2)) := by
          nlinarith only [mul_nonneg (mul_nonneg ha.le (sq_nonneg c)) (sq_nonneg p.2)]
        _ ≤ p.2 := hV
        _ ≤ a*2 := hy.2.trans_eq (mul_comm _ _)
    have hAbs : |c*p.1| ≤ 2 := by
      by_contra! h
      nlinarith only [h,hx,sq_abs (c*p.1),sq_nonneg (|c*p.1|-2)]
    have hx' : |p.1| ≤ 2/c := by
      apply (le_div_iff₀ hc).mpr
      rw [abs_mul,abs_of_pos hc,mul_comm] at hAbs
      exact hAbs
    exact ⟨⟨abs_le.mp hx',hy⟩,hv⟩
  have hZ : (∫ p in U, D p) = ∫ p in Q, D p :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUc hQU
      (fun p hp => by by_contra hn; exact hp.2 (hplace p hp.1 hn).1)
  have hPt (p : ℝ×ℝ) (hp : p ∈ Q) : ‖D p‖ ≤ 2*M₁*M₂/a := by
    by_cases hz : D p = 0
    · rw [hz,norm_zero]
      positivity
    have hv := (hplace p (hQU hp) hz).2
    have hy := hp.2
    have hyInv : (p.2^2)⁻¹ ≤ (a^2)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hy.1 2)
    have hρB : ‖ρ p.2‖ ≤ Real.sqrt (2*a)*M₁ :=
      (hρM _ hy).trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hy.2) hM₁)
    have hηB : ‖η (V p)‖ ≤ Real.sqrt (2*a)*M₂ :=
      (hηM _ hv).trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv.2) hM₂)
    have hnorm : ‖D p‖ = (p.2^2)⁻¹*(‖ρ p.2‖*‖η (V p)‖) := by
      dsimp only [D,weylPlanarDensity,weylPlanarIntegrand,weylPlanarAmplitude,V]
      rw [norm_smul,Real.norm_of_nonneg (by positivity),norm_mul,atkinPhase_norm,mul_one,
        Complex.norm_real,norm_mul]
    rw [hnorm]
    calc
      _ ≤ (a^2)⁻¹*((Real.sqrt (2*a)*M₁)*(Real.sqrt (2*a)*M₂)) :=
        mul_le_mul hyInv (mul_le_mul hρB hηB (norm_nonneg _) (by positivity))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (a^2)⁻¹*((Real.sqrt (2*a))^2*M₁*M₂) := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by positivity)]
        field_simp [ha.ne']
  have hvol : (volume Q).toReal = (4/c)*a := by
    change (((volume : Measure ℝ).prod volume) Q).toReal = _
    dsimp only [Q]
    rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [div_pos (by norm_num : (0:ℝ)<2) hc] : 0 ≤ 2/c-(-(2/c))),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*a-a)]
    ring
  rw [cuspWeylOrbitalKernel_coordinates,hZ]
  calc
    _ ≤ ∫ p in Q, ‖D p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _p in Q, 2*M₁*M₂/a :=
      setIntegral_mono_on (hi.mono_set hQU).norm (integrableOn_const hQc.measure_ne_top)
        hQc.measurableSet hPt
    _ = _ := by
      rw [integral_const,Measure.real_def,Measure.restrict_apply_univ,smul_eq_mul,hvol]
      field_simp [ha.ne',hc.ne']
      ring

end ArtinMatthews
