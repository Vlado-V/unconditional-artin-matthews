module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase
public import OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
public import OAI.RepresentationTheory.Weil.Local.PlanarRadialIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! # Planar Power Damping -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping.Construction

noncomputable section

/-! Integrability and local convergence of the actual complex norm-power damping. -/

open _root_.MeasureTheory Filter Set
open scoped _root_.Topology

def planarPowerDamping (s ε b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) : ℂ) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z

theorem planarPowerDamping_norm (s ε b : ℝ) (z : ℝ × ℝ) :
    ‖planarPowerDamping s ε b z‖ = Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) := by
  rw [planarPowerDamping, norm_mul, PlanarQuadraticPhase.Construction.planarQuadraticPhase_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem planarPowerDamping_continuous (s ε b : ℝ) (hs : 0 < s) :
    Continuous (planarPowerDamping s ε b) := by
  have ht : Continuous PlanarRadialCompact.Construction.planarRadiusSquared := by unfold PlanarRadialCompact.Construction.planarRadiusSquared; fun_prop
  have he := ((ht.rpow_const (fun _ => Or.inr hs.le)).const_mul (-ε)).rexp
  exact (Complex.continuous_ofReal.comp he).mul (PlanarQuadraticPhase.Construction.planarQuadraticPhase_continuous b)

theorem planar_power_weight_integrable (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (fun z : ℝ × ℝ => (Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) : ℂ)) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-ε * t ^ s)) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hs hε
  exact PlanarRadialIntegral.Construction.planarRadial_integrable (fun t => (Real.exp (-ε * t ^ s) : ℂ)) hi.ofReal

theorem planarPowerDamping_integrable (s ε b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (planarPowerDamping s ε b) := by
  apply (planar_power_weight_integrable s ε hs hε).norm.mono'
    (planarPowerDamping_continuous s ε b hs).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [planarPowerDamping_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem planarPowerDamping_norm_le (s ε b : ℝ) (hε : 0 ≤ ε) (z : ℝ × ℝ) :
    ‖planarPowerDamping s ε b z‖ ≤ 1 := by
  rw [planarPowerDamping_norm, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε)
    (Real.rpow_nonneg (PlanarRadialCompact.Construction.planarRadiusSquared_nonneg z) s)

theorem planarPowerDamping_tendsto (s b : ℝ) (z : ℝ × ℝ) :
    Tendsto (fun ε => planarPowerDamping s ε b z) (𝓝[>] (0 : ℝ)) (𝓝 (PlanarQuadraticPhase.Construction.planarQuadraticPhase b z)) := by
  have hc : ContinuousAt (fun ε => planarPowerDamping s ε b z) 0 := by
    unfold planarPowerDamping
    fun_prop
  simpa only [planarPowerDamping, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem planarPowerDamping_complex (s ε : ℝ) (z : ℂ) :
    planarPowerDamping s ε Real.pi (z.re, z.im) =
      (Real.exp (-ε * ‖z‖ ^ (2 * s)) : ℂ) * ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) := by
  rw [planarPowerDamping, PlanarQuadraticPhase.Construction.planarQuadraticPhase_standard]
  have hnorm : PlanarRadialCompact.Construction.planarRadiusSquared (z.re, z.im) = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp [PlanarRadialCompact.Construction.planarRadiusSquared, Complex.normSq_apply, pow_two]
  rw [hnorm, Real.rpow_mul (norm_nonneg z), Real.rpow_two]

end

end OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping.Construction
