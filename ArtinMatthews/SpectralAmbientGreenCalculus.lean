module

public import ArtinMatthews.SpectralGamma0AmbientResolventAnalytic
public import ArtinMatthews.SpectralContinuousQuadraticMeasure
public import ArtinMatthews.SpectralGamma0FormOperator
public import ArtinMatthews.SpectralContinuousQuadraticIntegral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
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

/-! The actual full ambient resolvent is the genuine continuous
functional-calculus resolvent of the positive bounded Green operator. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0Green_spectrum_complex_mem_real_unit (N : ℕ) [NeZero N]
    {z : ℂ} (hz : z∈spectrum ℂ (gamma0Green N)) :
    ∃ x : ℝ, 0≤x ∧ x≤1 ∧ z=(x:ℂ) := by
  have hR : SpectrumRestricts (gamma0Green N) Complex.reCLM :=
    IsSelfAdjoint.spectrumRestricts (a:=gamma0Green N) (gamma0Green_selfAdjoint N)
  obtain ⟨x,hx,hzx⟩ := hR.algebraMap_image ▸ hz
  have he : (x:ℂ)=z := hzx
  have h0 : 0≤x := spectrum_nonneg_of_nonneg
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (gamma0Green_positive N)) hx
  have h1 : ‖(1:Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N)‖≤1 := ContinuousLinearMap.norm_id_le
  have hnorm : ‖z‖≤1 := (spectrum.norm_le_norm_mul_of_mem hz).trans
    (by simpa only [one_mul] using mul_le_mul (gamma0Green_norm N) h1 (norm_nonneg _) zero_le_one)
  rw [← he,Complex.norm_real,Real.norm_of_nonneg h0] at hnorm
  exact ⟨x,h0,hnorm,he.symm⟩

theorem gamma0Green_spectrum_resolvent_denominator_ne_zero (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (x : spectrum ℂ (gamma0Green N)) :
    1-(z+1)*(x:ℂ)≠0 := by
  obtain ⟨r,hr,hr1,hx⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  rw [hx]
  intro h
  have hM : (z+1)*(r:ℂ)=1 := (sub_eq_zero.mp h).symm
  have hr0 : r≠0 := by
    intro he
    simp [he] at hM
  have hrp : 0<r := lt_of_le_of_ne hr hr0.symm
  have hEq : z+1=1/(r:ℂ) := (eq_div_iff (Complex.ofReal_ne_zero.mpr hr0)).mpr hM
  have hReal : z=((r⁻¹-1:ℝ):ℂ) := by
    rw [Complex.ofReal_sub,Complex.ofReal_inv,Complex.ofReal_one,← one_div]
    exact eq_sub_of_add_eq hEq
  have hNonneg : 0≤r⁻¹-1 := by
    apply sub_nonneg.mpr
    rw [← one_div]
    exact (le_div_iff₀ hrp).mpr (by simpa only [one_mul] using hr1)
  rw [hReal,Complex.ofReal_re,Complex.norm_real,Real.norm_of_nonneg hNonneg] at hz
  exact (lt_irrefl _ hz)

def gamma0GreenSpectrumCoordinate (N : ℕ) [NeZero N] : C(spectrum ℂ (gamma0Green N),ℂ) :=
  (ContinuousMap.id ℂ).restrict (spectrum ℂ (gamma0Green N))

def gamma0GreenResolventSymbol (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) : C(spectrum ℂ (gamma0Green N),ℂ) :=
  ⟨fun x => (x:ℂ)/(1-(z+1)*(x:ℂ)),
    continuous_subtype_val.div (continuous_const.sub (continuous_const.mul continuous_subtype_val))
      (gamma0Green_spectrum_resolvent_denominator_ne_zero N z hz)⟩

def gamma0GreenResolventDenominator (N : ℕ) [NeZero N] (z : ℂ) :
    C(spectrum ℂ (gamma0Green N),ℂ) :=
  1-(z+1) • gamma0GreenSpectrumCoordinate N

theorem gamma0GreenResolventDenominator_apply (N : ℕ) [NeZero N]
    (z : ℂ) (x : spectrum ℂ (gamma0Green N)) :
    gamma0GreenResolventDenominator N z x=1-(z+1)*(x:ℂ) := rfl

theorem gamma0GreenResolventDenominator_isUnit (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) : IsUnit (gamma0GreenResolventDenominator N z) := by
  let D := gamma0GreenResolventDenominator N z
  let I : C(spectrum ℂ (gamma0Green N),ℂ) :=
    ⟨fun x => (D x)⁻¹,D.continuous.inv₀ (gamma0Green_spectrum_resolvent_denominator_ne_zero N z hz)⟩
  have h : D*I=1 := by
    ext x
    change D x*(D x)⁻¹=1
    exact mul_inv_cancel₀ (gamma0Green_spectrum_resolvent_denominator_ne_zero N z hz x)
  exact ⟨Units.mkOfMulEqOne D I h,rfl⟩

theorem gamma0GreenResolventDenominator_mul_symbol (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) :
    gamma0GreenResolventDenominator N z*gamma0GreenResolventSymbol N z hz=gamma0GreenSpectrumCoordinate N := by
  ext x
  change (1-(z+1)*(x:ℂ))*((x:ℂ)/(1-(z+1)*(x:ℂ)))=(x:ℂ)
  field_simp [gamma0Green_spectrum_resolvent_denominator_ne_zero N z hz x]

theorem gamma0AmbientResolventFamily_green_pencil (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) :
    (1-(z+1) • gamma0Green N)*gamma0AmbientResolventFamily N z=gamma0Green N := by
  apply ContinuousLinearMap.ext
  intro F
  let u := gamma0AmbientWeakResolvent N z hz F
  let J := gamma0EnergyInclusion N
  let Jstar := gamma0EnergyMassAdjoint N
  have h := congrArg J (gamma0AmbientWeakResolvent_pencil N z hz F)
  change J (u-(z+1) • Jstar (J u))=J (Jstar F) at h
  rw [map_sub,map_smul] at h
  rw [gamma0AmbientResolventFamily_eq N z hz]
  change J u-(z+1) • J (Jstar (J u))=J (Jstar F)
  exact h

theorem gamma0AmbientResolventFamily_eq_cfc (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) :
    gamma0AmbientResolventFamily N z=
      cfcHom (gamma0Green_selfAdjoint N).isStarNormal (gamma0GreenResolventSymbol N z hz) := by
  let C := cfcHom (R:=ℂ) (gamma0Green_selfAdjoint N).isStarNormal
  let D := gamma0GreenResolventDenominator N z
  let F := gamma0GreenResolventSymbol N z hz
  have hid : C (gamma0GreenSpectrumCoordinate N)=gamma0Green N := cfcHom_id _
  have hD : C D=1-(z+1) • gamma0Green N := by
    change C (1-(z+1) • gamma0GreenSpectrumCoordinate N)=_
    rw [map_sub,map_smul,map_one,hid]
  have hunit : IsUnit (C D) := (gamma0GreenResolventDenominator_isUnit N z hz).map C
  apply hunit.mul_left_cancel
  calc
    C D*gamma0AmbientResolventFamily N z=gamma0Green N := by
      rw [hD]
      exact gamma0AmbientResolventFamily_green_pencil N z hz
    _ = C D*C F := by
      rw [← map_mul,gamma0GreenResolventDenominator_mul_symbol N z hz,hid]

theorem gamma0AmbientResolventFamily_quadratic_integral (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (u : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientResolventFamily N z u)=
      ∫ x, (x:ℂ)/(1-(z+1)*(x:ℂ)) ∂spectralQuadraticMeasure (gamma0Green N)
        (gamma0Green_selfAdjoint N).isStarNormal u := by
  rw [gamma0AmbientResolventFamily_eq_cfc N z hz]
  exact (spectralQuadraticMeasure_integral_complex (gamma0Green N)
    (gamma0Green_selfAdjoint N).isStarNormal u (gamma0GreenResolventSymbol N z hz)).symm

end ArtinMatthews
