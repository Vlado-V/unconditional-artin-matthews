module

public import ArtinMatthews.SpectralWeylCosineKernel
public import ArtinMatthews.SpectralWeylHeightJacobian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Evaluation of the actual Weyl orbital integral as its explicit two-height
cosine kernel, including the square-root denominator and integration region. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def weylTwoHeightDensity (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ) (c : ℝ)
    (y v : ℝ) : ℂ :=
  (ρ y * η v / (c^2*y*v^2*weylHeightRoot c y v) *
    Real.cos (2*Real.pi*((m : ℝ)+(n : ℝ)*v/y)*weylHeightRoot c y v/(N : ℝ)) : ℝ)

theorem weylPlanarPhase_heightRoot (N : ℕ) (m n : ℤ) {c y v : ℝ}
    (hc : c ≠ 0) (hy : 0 < y) (hv : v ∈ Ioo 0 (1/(c^2*y))) :
    weylPlanarPhase N m n c (weylHeightRoot c y v) y =
      -(((m : ℝ)+(n : ℝ)*v/y)*weylHeightRoot c y v/(N : ℝ)) := by
  have hh := weylSecondHeight_heightRoot hc hy hv
  have hi : (c^2*((weylHeightRoot c y v)^2+y^2))⁻¹ = v/y := by
    apply (eq_div_iff hy.ne').mpr
    simpa only [weylSecondHeight,div_eq_mul_inv,mul_comm] using hh
  unfold weylPlanarPhase
  simp only [div_eq_mul_inv,hi]
  ring

theorem weylTwoHeightDensity_jacobian (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hv : v ∈ Ioo 0 (1/(c^2*y))) :
    2 * (weylHeightJacobian c y v •
      weylCosineDensity N m n ρ η c (weylHeightRoot c y v,y)) =
      weylTwoHeightDensity N m n ρ η c y v := by
  have hh := weylSecondHeight_heightRoot hc hy hv
  have hr := (weylHeightRoot_pos hc hy hv).ne'
  unfold weylCosineDensity weylPlanarAmplitude
  change 2 * (weylHeightJacobian c y v •
    ((ρ y * η (weylSecondHeight c y (weylHeightRoot c y v)) / y^2 *
      Real.cos (2*Real.pi*weylPlanarPhase N m n c (weylHeightRoot c y v) y) : ℝ) : ℂ)) = _
  rw [hh,weylPlanarPhase_heightRoot N m n hc hy hv,mul_neg,Real.cos_neg]
  unfold weylHeightJacobian weylTwoHeightDensity
  rw [Complex.real_smul]
  push_cast
  field_simp [hc,hy.ne',hv.1.ne',hr]

theorem weylCosine_height_integral (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    {c y : ℝ} (hc : c ≠ 0) (hy : 0 < y) :
    2 * (∫ x in Ioi (0 : ℝ), weylCosineDensity N m n ρ η c (x,y)) =
      ∫ v in Ioo 0 (1/(c^2*y)), weylTwoHeightDensity N m n ρ η c y v := by
  rw [weylHeight_integral_substitution hc hy,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  exact weylTwoHeightDensity_jacobian N m n ρ η hc hy hv

theorem cuspWeylOrbitalKernel_twoHeight (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2}) :
    cuspWeylOrbitalKernel N m n ρ η c hc =
      ∫ y in Ioi (0 : ℝ), ∫ v in Ioo 0 (1/(c^2*y)),
        weylTwoHeightDensity N m n ρ η c y v := by
  rw [cuspWeylOrbitalKernel_cosine N m n ρ η c hc hI,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact weylCosine_height_integral N m n ρ η hc hy

theorem weylPlanarDensity_integrable_of_orbital (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hI : Integrable (cuspWeylOrbitalIntegrand N m n ρ η c hc)) :
    IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2} := by
  apply (upperHalfPlane_integrable_coordinates_smul _).mp
  apply hI.congr
  exact Eventually.of_forall (cuspWeylOrbitalIntegrand_coordinates N m n ρ η c hc)

theorem weylCosine_horizontal_integrable (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c y : ℝ) (hI : Integrable (fun x : ℝ => weylPlanarDensity N m n ρ η c (x,y))) :
    IntegrableOn (fun x : ℝ => weylCosineDensity N m n ρ η c (x,y)) (Ioi (0 : ℝ)) := by
  have hp : IntegrableOn (fun x : ℝ => weylPlanarDensity N m n ρ η c (x,y)) (Ioi (0 : ℝ)) :=
    hI.restrict
  have hh := ((integrable_complex_star hp).add hp).const_mul (1/2 : ℂ)
  apply hh.congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  rw [weylPlanarDensity_reflection_pair]
  ring

theorem weylTwoHeight_integrable_ae (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2}) :
    ∀ᵐ y ∂volume.restrict (Ioi (0 : ℝ)),
      IntegrableOn (weylTwoHeightDensity N m n ρ η c y) (Ioo 0 (1/(c^2*y))) := by
  have hs : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by ext p; simp
  rw [hs] at hI
  change Integrable _ ((volume.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ))) at hI
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hI
  filter_upwards [hI.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with y hFy hy
  have hcos := weylCosine_horizontal_integrable N m n ρ η c y hFy
  have htr := (weylHeight_integrable_substitution hc hy
    (fun x => weylCosineDensity N m n ρ η c (x,y))).mp hcos
  apply (htr.const_mul (2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  exact weylTwoHeightDensity_jacobian N m n ρ η hc hy hv

end ArtinMatthews
