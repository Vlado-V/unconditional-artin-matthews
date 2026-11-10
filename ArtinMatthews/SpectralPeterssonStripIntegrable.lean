module

public import ArtinMatthews.SpectralPeterssonPairingUnfold
public import ArtinMatthews.SpectralWeylPlanarCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute integrability of the actual normalized strip pairing,
using the Petersson-weighted pointwise norm and the Gamma envelope. -/

noncomputable section
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem spectralPetersson_gammaEnvelope_integrable (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y^(a-1)*Real.exp (-(r*y))) (Ioi 0) := by
  let f (y : ℝ) := y^(a-1)*Real.exp (-y)
  have hf : IntegrableOn f (Ioi 0) := by
    simpa only [f,mul_comm] using Real.GammaIntegral_convergent ha
  have hs := (integrableOn_Ioi_comp_mul_left_iff f 0 hr).mpr (by simpa only [mul_zero] using hf)
  have hs' : IntegrableOn (fun y => r^(1-a)*f (r*y)) (Ioi 0) := hs.const_mul (r^(1-a))
  refine hs'.congr_fun ?_ measurableSet_Ioi
  intro y hy
  change r^(1-a)*((r*y)^(a-1)*Real.exp (-(r*y))) = y^(a-1)*Real.exp (-(r*y))
  rw [Real.mul_rpow hr.le hy.le,← mul_assoc,← mul_assoc,← Real.rpow_add hr,
    show 1-a+(a-1)=0 by ring,Real.rpow_zero,one_mul]

def spectralPeterssonCoordinatePoint (p : ℝ × ℝ) : UpperHalfPlane :=
  ofComplex ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I)

theorem spectralPeterssonCoordinatePoint_im (p : ℝ × ℝ) (hp : 0 < p.2) :
    (spectralPeterssonCoordinatePoint p).im = p.2 := by
  unfold spectralPeterssonCoordinatePoint
  rw [ofComplex_apply_of_im_pos (by simp [hp])]
  simp

theorem spectralPeterssonCoordinatePoint_at (z : UpperHalfPlane) :
    spectralPeterssonCoordinatePoint (z.re,z.im) = z := by
  unfold spectralPeterssonCoordinatePoint
  rw [show ((z.re : ℂ)+(z.im : ℂ)*Complex.I) = (z : ℂ) from Complex.re_add_im _,
    ofComplex_apply]

theorem spectralPeterssonCoordinatePoint_continuousOn :
    ContinuousOn spectralPeterssonCoordinatePoint {p : ℝ × ℝ | 0 < p.2} := by
  apply UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr
  have h : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ)+(p.2 : ℂ)*Complex.I) := by fun_prop
  refine h.continuousOn.congr ?_
  intro p hp
  have hpos : 0 < p.2 := hp
  dsimp only [Function.comp_def,spectralPeterssonCoordinatePoint]
  rw [ofComplex_apply_of_im_pos (by simp [hpos])]

def spectralPeterssonStripCoordinates (k : ℕ) (n : ℕ+) (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ :=
  UpperHalfPlane.petersson (k : ℤ) (spectralHolomorphicCuspSeed (n : ℕ)) F
    (spectralPeterssonCoordinatePoint p)

theorem spectralPeterssonStripCoordinates_weighted_integrable (k : ℕ) (hk : 3 ≤ k) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) :
    IntegrableOn (fun p : ℝ × ℝ => (p.2^2)⁻¹ • spectralPeterssonStripCoordinates k n F p)
      ((Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))) (volume.prod volume) := by
  let S := (Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))
  let U := {p : ℝ × ℝ | 0 < p.2}
  let G (p : ℝ × ℝ) := (p.2^2)⁻¹ • spectralPeterssonStripCoordinates k n F p
  let r := 2*Real.pi*(n : ℝ)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hr : 0 < r := mul_pos (mul_pos two_pos Real.pi_pos) hn
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hγ : IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)*Real.exp (-(r*y))) (Ioi 0) := by
    have h := spectralPetersson_gammaEnvelope_integrable ((k : ℝ)/2-1) r (by linarith) hr
    simpa only [show (k : ℝ)/2-1-1=(k : ℝ)/2-2 by ring] using h
  have hEnv : IntegrableOn (fun p : ℝ × ℝ => M*(p.2^((k : ℝ)/2-2)*Real.exp (-(r*p.2)))) S
      (volume.prod volume) := by
    rw [IntegrableOn,← Measure.prod_restrict]
    let _ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    have hx : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)) := integrable_const _
    simpa only [one_mul] using hx.mul_prod (hγ.const_mul M)
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hSU : S ⊆ U := fun _ hp => hp.2
  have hseed : Continuous (spectralHolomorphicCuspSeed (n : ℕ)) := by
    unfold spectralHolomorphicCuspSeed
    fun_prop
  have hP : ContinuousOn (spectralPeterssonStripCoordinates k n F) U :=
    (UpperHalfPlane.petersson_continuous (k : ℤ) hseed hF).continuousOn.comp
      spectralPeterssonCoordinatePoint_continuousOn (fun _ _ => Set.mem_univ _)
  have hInv : ContinuousOn (fun p : ℝ × ℝ => (p.2^2)⁻¹) U :=
    (continuous_snd.pow 2).continuousOn.inv₀ (fun _ hp => pow_ne_zero _ (ne_of_gt hp))
  have hG : ContinuousOn G U := hInv.smul hP
  refine hEnv.mono' ((hG.mono hSU).aestronglyMeasurable hS) ?_
  filter_upwards [ae_restrict_mem (μ := volume.prod volume) hS] with p hp
  let z := spectralPeterssonCoordinatePoint p
  have hy : 0 < p.2 := hp.2
  have hz : z.im = p.2 := spectralPeterssonCoordinatePoint_im p hy
  have hweight : (p.2^2)⁻¹*p.2^k = p.2^((k : ℝ)/2)*p.2^((k : ℝ)/2-2) := by
    rw [mul_comm,← div_eq_mul_inv,← Real.rpow_natCast,← Real.rpow_natCast,
      ← Real.rpow_sub hy,← Real.rpow_add hy]
    congr 1
    norm_num
    ring
  have hnorm : ‖G p‖ = (‖F z‖*p.2^((k : ℝ)/2))*(p.2^((k : ℝ)/2-2)*Real.exp (-(r*p.2))) := by
    dsimp only [G,spectralPeterssonStripCoordinates]
    rw [norm_smul,Real.norm_of_nonneg (by positivity),UpperHalfPlane.petersson]
    simp only [norm_mul,Complex.norm_conj,spectralHolomorphicCuspSeed_norm,zpow_natCast,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg (spectralPeterssonCoordinatePoint p).im_pos.le]
    change (p.2^2)⁻¹*(Real.exp (-(r*z.im))*‖F z‖*z.im^k) = _
    rw [hz,show (p.2^2)⁻¹*(Real.exp (-(r*p.2))*‖F z‖*p.2^k) =
      ‖F z‖*((p.2^2)⁻¹*p.2^k)*Real.exp (-(r*p.2)) by ring,hweight]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (by simpa only [hz] using hbd z)
    (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_nonneg _))

theorem spectralPeterssonStripIntegrand_integrable (k : ℕ) (hk : 3 ≤ k) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) :
    Integrable (spectralPeterssonStripIntegrand k n F) := by
  let S := (Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))
  let G := spectralPeterssonStripCoordinates k n F
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hp.2
  have he : spectralPeterssonStripIntegrand k n F = fun z => S.indicator G (z.re,z.im) := by
    funext z
    unfold spectralPeterssonStripIntegrand
    have hmem : z ∈ hyperbolicCuspStrip 1 0 ↔ (z.re,z.im) ∈ S := Iff.rfl
    by_cases hz : (z.re,z.im) ∈ S
    · rw [indicator_of_mem (hmem.mpr hz),indicator_of_mem hz]
      simp only [G,spectralPeterssonStripCoordinates,spectralPeterssonCoordinatePoint_at]
    · rw [indicator_of_notMem (fun h => hz (hmem.mp h)),indicator_of_notMem hz]
  rw [he,upperHalfPlane_integrable_coordinates_smul]
  have hind : (fun p : ℝ × ℝ => (p.2^2)⁻¹ • S.indicator G p) =
      S.indicator (fun p => (p.2^2)⁻¹ • G p) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  rw [hind]
  change Integrable (S.indicator (fun p => (p.2^2)⁻¹ • G p))
    ((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2})
  rw [integrable_indicator_iff hS]
  change Integrable _ (((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}).restrict S)
  rw [Measure.restrict_restrict_of_subset hpos]
  exact spectralPeterssonStripCoordinates_weighted_integrable k hk n F hF M hbd

end ArtinMatthews
