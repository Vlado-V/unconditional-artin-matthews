module

public import ArtinMatthews.SpectralPeterssonHeckeUnfold
public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import ArtinMatthews.SpectralPeterssonStripIntegrable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates
public import ArtinMatthews.SpectralPeterssonReproducing
public import ArtinMatthews.SpectralWeylPlanarCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! Absolute strip integrability for each positive regulator and the
exact Gamma mass of the actual weight-two Petersson pairing. -/

noncomputable section
open MeasureTheory Set Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonHeckeSeed_continuous (u : ℝ) (n : ℕ+) :
    Continuous (spectralPeterssonHeckeSeed u n) := by
  have hy : Continuous (fun z : UpperHalfPlane => z.im^u) :=
    continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  have hseed : Continuous (spectralHolomorphicCuspSeed (n : ℕ)) := by
    unfold spectralHolomorphicCuspSeed
    fun_prop
  exact (Complex.continuous_ofReal.comp hy).mul hseed

theorem spectralPeterssonHeckeSeed_norm (u : ℝ) (n : ℕ+) (z : UpperHalfPlane) :
    ‖spectralPeterssonHeckeSeed u n z‖ = z.im^u * Real.exp (-(2*Real.pi*(n : ℝ)*z.im)) := by
  unfold spectralPeterssonHeckeSeed
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _),
    spectralHolomorphicCuspSeed_norm]

def spectralPeterssonHeckeStripCoordinates (u : ℝ) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  UpperHalfPlane.petersson 2 (spectralPeterssonHeckeSeed u n) F (spectralPeterssonCoordinatePoint p)

private def heckeStripCell : Set (ℝ × ℝ) := (Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))

private theorem heckeStripCell_measurable : MeasurableSet heckeStripCell :=
  measurableSet_Ioc.prod measurableSet_Ioi

private theorem heckeStripIntegrand_coordinates (u : ℝ) (n : ℕ+) (F : UpperHalfPlane → ℂ) :
    spectralPeterssonHeckeStripIntegrand u n F =
      fun z => heckeStripCell.indicator (spectralPeterssonHeckeStripCoordinates u n F) (z.re,z.im) := by
  funext z
  unfold spectralPeterssonHeckeStripIntegrand
  have hmem : z ∈ hyperbolicCuspStrip 1 0 ↔ (z.re,z.im) ∈ heckeStripCell := Iff.rfl
  by_cases hz : (z.re,z.im) ∈ heckeStripCell
  · rw [indicator_of_mem (hmem.mpr hz),indicator_of_mem hz]
    simp only [spectralPeterssonHeckeStripCoordinates,spectralPeterssonCoordinatePoint_at]
  · rw [indicator_of_notMem (fun h => hz (hmem.mp h)),indicator_of_notMem hz]

theorem spectralPeterssonHeckeStripCoordinates_integrable (u : ℝ) (hu : 0 < u) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ) (hbd : ∀ z, ‖F z‖*z.im ≤ M) :
    IntegrableOn (fun p : ℝ × ℝ => (p.2^2)⁻¹ • spectralPeterssonHeckeStripCoordinates u n F p)
      ((Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))) (volume.prod volume) := by
  let U := {p : ℝ × ℝ | 0 < p.2}
  let G (p : ℝ × ℝ) := (p.2^2)⁻¹ • spectralPeterssonHeckeStripCoordinates u n F p
  let r := 2*Real.pi*(n : ℝ)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hr : 0 < r := mul_pos (mul_pos two_pos Real.pi_pos) hn
  have hγ := spectralPetersson_gammaEnvelope_integrable u r hu hr
  have hEnv : IntegrableOn (fun p : ℝ × ℝ => M*(p.2^(u-1)*Real.exp (-(r*p.2)))) heckeStripCell
      (volume.prod volume) := by
    rw [heckeStripCell,IntegrableOn,← Measure.prod_restrict]
    let _ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    have hx : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)) := integrable_const _
    simpa only [one_mul] using hx.mul_prod (hγ.const_mul M)
  have hSU : heckeStripCell ⊆ U := fun _ hp => hp.2
  have hP : ContinuousOn (spectralPeterssonHeckeStripCoordinates u n F) U :=
    (UpperHalfPlane.petersson_continuous 2 (spectralPeterssonHeckeSeed_continuous u n) hF).continuousOn.comp
      spectralPeterssonCoordinatePoint_continuousOn (fun _ _ => Set.mem_univ _)
  have hInv : ContinuousOn (fun p : ℝ × ℝ => (p.2^2)⁻¹) U :=
    (continuous_snd.pow 2).continuousOn.inv₀ (fun _ hp => pow_ne_zero _ (ne_of_gt hp))
  have hG : ContinuousOn G U := hInv.smul hP
  change IntegrableOn G heckeStripCell (volume.prod volume)
  refine hEnv.mono' ((hG.mono hSU).aestronglyMeasurable heckeStripCell_measurable) ?_
  filter_upwards [ae_restrict_mem (μ := volume.prod volume) heckeStripCell_measurable] with p hp
  let z := spectralPeterssonCoordinatePoint p
  have hy : 0 < p.2 := hp.2
  have hz : z.im = p.2 := spectralPeterssonCoordinatePoint_im p hy
  have hpower := Real.rpow_add hy (1 : ℝ) (u-1)
  rw [show 1+(u-1) = u by ring,Real.rpow_one] at hpower
  have hnz : ‖(p.2 : ℂ)^(2 : ℤ)‖ = p.2^2 := by
    change ‖(p.2 : ℂ)^(2 : ℕ)‖ = _
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg hy.le]
  have hnorm : ‖G p‖ = (‖F z‖*p.2)*(p.2^(u-1)*Real.exp (-(r*p.2))) := by
    change ‖(p.2^2)⁻¹ • UpperHalfPlane.petersson 2 (spectralPeterssonHeckeSeed u n) F z‖ = _
    rw [norm_smul,Real.norm_of_nonneg (by positivity),UpperHalfPlane.petersson]
    simp only [norm_mul,Complex.norm_conj,spectralPeterssonHeckeSeed_norm,hz,hnz]
    change (p.2^2)⁻¹*((p.2^u*Real.exp (-(r*p.2)))*‖F z‖*p.2^2) = _
    rw [hpower]
    field_simp [hy.ne']
    <;> ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (by simpa only [hz] using hbd z)
    (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_nonneg _))

theorem spectralPeterssonHeckeStripIntegrand_integrable (u : ℝ) (hu : 0 < u) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ) (hbd : ∀ z, ‖F z‖*z.im ≤ M) :
    Integrable (spectralPeterssonHeckeStripIntegrand u n F) := by
  let G := spectralPeterssonHeckeStripCoordinates u n F
  have hpos : heckeStripCell ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hp.2
  rw [heckeStripIntegrand_coordinates,upperHalfPlane_integrable_coordinates_smul]
  have hind : (fun p : ℝ × ℝ => (p.2^2)⁻¹ • heckeStripCell.indicator G p) =
      heckeStripCell.indicator (fun p => (p.2^2)⁻¹ • G p) := by
    funext p
    by_cases hp : p ∈ heckeStripCell <;> simp [hp]
  rw [hind]
  change Integrable (heckeStripCell.indicator (fun p => (p.2^2)⁻¹ • G p))
    ((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2})
  rw [integrable_indicator_iff heckeStripCell_measurable]
  change Integrable _ (((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}).restrict heckeStripCell)
  rw [Measure.restrict_restrict_of_subset hpos]
  exact spectralPeterssonHeckeStripCoordinates_integrable u hu n F hF M hbd

theorem spectralPeterssonHeckeStripCoordinate_slice (u : ℝ) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in Ioc (0 : ℝ) 1, (y^2)⁻¹ • spectralPeterssonHeckeStripCoordinates u n F (x,y)) =
      ((y^u*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*spectralPeterssonFourierAtHeight F n y hy := by
  let c := ((y^u : ℝ) : ℂ)
  have he (x : ℝ) : (y^2)⁻¹ • spectralPeterssonHeckeStripCoordinates u n F (x,y) =
      c*((y^2)⁻¹ • spectralPeterssonStripCoordinates 2 n F (x,y)) := by
    unfold spectralPeterssonHeckeStripCoordinates spectralPeterssonStripCoordinates
      UpperHalfPlane.petersson spectralPeterssonHeckeSeed
    have hy' : (spectralPeterssonCoordinatePoint (x,y)).im = y :=
      spectralPeterssonCoordinatePoint_im (x,y) hy
    simp only [hy',map_mul,Complex.conj_ofReal,RCLike.real_smul_eq_coe_mul]
    change _ = ((y^u : ℝ) : ℂ)*_
    ring
  calc
    _ = ∫ x in Ioc (0 : ℝ) 1, c*((y^2)⁻¹ • spectralPeterssonStripCoordinates 2 n F (x,y)) :=
      setIntegral_congr_fun measurableSet_Ioc (fun x _ => he x)
    _ = c*(∫ x in Ioc (0 : ℝ) 1, (y^2)⁻¹ • spectralPeterssonStripCoordinates 2 n F (x,y)) :=
      integral_const_mul _ _
    _ = _ := by
      rw [spectralPeterssonStripCoordinate_slice 2 le_rfl n F y hy]
      simp only [Nat.sub_self,pow_zero,one_mul,Complex.ofReal_mul,c,mul_assoc]

def spectralPeterssonHeckeMass (u : ℝ) (n : ℕ+) : ℝ :=
  Real.Gamma (1+u)/(4*Real.pi*(n : ℝ))^(1+u)

theorem spectralPeterssonHeckeMass_integral (u : ℝ) (hu : -1 < u) (n : ℕ+) :
    (∫ y in Ioi (0 : ℝ), y^u*Real.exp (-(4*Real.pi*(n : ℝ)*y))) =
      spectralPeterssonHeckeMass u n := by
  let r := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp only [r]; positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1+u) (by linarith) hr
  rw [show 1+u-1=u by ring,one_div,Real.inv_rpow hr.le] at h
  change (∫ y in Ioi (0 : ℝ), y^u*Real.exp (-(r*y))) = Real.Gamma (1+u)/r^(1+u)
  rw [h,div_eq_mul_inv,mul_comm]

theorem spectralPeterssonHeckeStrip_reproduce (u : ℝ) (hu : 0 < u) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ) (hbd : ∀ z, ‖F z‖*z.im ≤ M)
    (A : ℂ) (hA : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight F n y hy = A) :
    (∫ z, spectralPeterssonHeckeStripIntegrand u n F z) = (spectralPeterssonHeckeMass u n : ℂ)*A := by
  let G := spectralPeterssonHeckeStripCoordinates u n F
  let I (p : ℝ × ℝ) := (p.2^2)⁻¹ • G p
  have hpos : heckeStripCell ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hp.2
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ heckeStripCell} :=
    heckeStripCell_measurable.preimage (by fun_prop)
  rw [heckeStripIntegrand_coordinates]
  change (∫ z, {z : UpperHalfPlane | (z.re,z.im) ∈ heckeStripCell}.indicator (fun z => G (z.re,z.im)) z) = _
  rw [integral_indicator hpre,upperHalfPlane_setIntegral_coordinates_smul G heckeStripCell_measurable hpos]
  change (∫ p in (Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ)), I p ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hI : Integrable I ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact spectralPeterssonHeckeStripCoordinates_integrable u hu n F hF M hbd
  rw [integral_prod_symm I hI]
  calc
    _ = ∫ y in Ioi (0 : ℝ), ((y^u*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*A := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (spectralPeterssonHeckeStripCoordinate_slice u n F y hy).trans (by rw [hA y hy])
    _ = _ := by
      rw [integral_mul_const,integral_complex_ofReal,spectralPeterssonHeckeMass_integral u (by linarith)]

theorem gamma0PeterssonInner_hecke_reproduce (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (u : ℝ) (hu : 0 < u) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash 2 (atkinRealMap γ.val) F = F)
    (hCont : Continuous (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N a) F)) (M : ℝ)
    (hbd : ∀ z, ‖spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N a) F z‖*z.im ≤ M)
    (A : ℂ) (hA : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N a) F) n y hy = A) :
    gamma0PeterssonInner N 2 (gamma0PeterssonHecke N a u n) F = (spectralPeterssonHeckeMass u n : ℂ)*A := by
  rw [gamma0PeterssonInner_hecke_unfold N a u n F hF
    (spectralPeterssonHeckeStripIntegrand_integrable u hu n _ hCont M hbd)]
  exact spectralPeterssonHeckeStrip_reproduce u hu n _ hCont M hbd A hA

end ArtinMatthews
