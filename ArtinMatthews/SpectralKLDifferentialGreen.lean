module

public import ArtinMatthews.SpectralKLCompactDifferential
public import ArtinMatthews.SpectralKLCompactOrder
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.SpectralBesselKEquation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology ContDiff
noncomputable section

def spectralKFlux (ν : ℂ) (x : ℝ) : ℂ := (x : ℂ) * deriv (schlafliBesselK ν) x

theorem spectralKFlux_hasDerivAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (spectralKFlux ν)
      (((x : ℂ) ^ 2 + ν ^ 2) / (x : ℂ) * schlafliBesselK ν x) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    convert (hasDerivAt_id x).ofReal_comp using 1
    rfl
  have h := hid.mul (schlafliBesselK_deriv_hasDerivAt ν x hx)
  rw [← schlafliBesselK_second_deriv ν x hx] at h
  have he : deriv (schlafliBesselK ν) x + (x : ℂ) * deriv (deriv (schlafliBesselK ν)) x =
      ((x : ℂ) ^ 2 + ν ^ 2) / (x : ℂ) * schlafliBesselK ν x := by
    calc
      _ = (((x : ℂ) ^ 2 + ν ^ 2) * schlafliBesselK ν x) / (x : ℂ) := by
        apply (eq_div_iff hx0).mpr
        linear_combination schlafliBesselK_modifiedBesselODE ν x hx
      _ = _ := by ring
  convert h using 1
  · rfl
  · simpa only [Complex.ofReal_one, id_eq, one_mul] using he.symm

theorem spectralKLCompactOrderTransform_operator (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    spectralKLCompactOrderTransform (spectralKLPhysicalOperator g) ν =
      -(ν ^ 2) * spectralKLCompactOrderTransform g ν := by
  let k := schlafliBesselK ν
  let flux := spectralKLCompactFlux g
  let v := spectralKFlux ν
  let v' := fun x : ℝ => (((x : ℂ) ^ 2 + ν ^ 2) / (x : ℂ)) * k x
  let w := fun x : ℝ => (x : ℂ) * k x
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hflux := spectralKLCompactFlux_smooth g hg
  have hflux' := (contDiff_infty_iff_deriv.mp hflux).2
  have hcflux : HasCompactSupport flux := hc.deriv.mul_left
  have hpflux : tsupport flux ⊆ Ioi (0 : ℝ) := (spectralKLCompactFlux_tsupport g).trans hp
  have hpg' : tsupport (deriv g) ⊆ Ioi (0 : ℝ) := tsupport_deriv_subset.trans hp
  have hpflux' : tsupport (deriv flux) ⊆ Ioi (0 : ℝ) := tsupport_deriv_subset.trans hpflux
  have hk (x : ℝ) (hx : 0 < x) : ContinuousAt k x :=
    (schlafliBesselK_hasDerivAt ν x hx).continuousAt
  have hk' (x : ℝ) (hx : 0 < x) : ContinuousAt (deriv k) x :=
    (schlafliBesselK_deriv_hasDerivAt ν x hx).continuousAt
  have hv (x : ℝ) (hx : 0 < x) : ContinuousAt v x := (spectralKFlux_hasDerivAt ν hx).continuousAt
  have hv' (x : ℝ) (hx : 0 < x) : ContinuousAt v' x :=
    (((Complex.continuous_ofReal.continuousAt.pow 2).add continuousAt_const).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hx.ne')).mul (hk x hx)
  have hw (x : ℝ) (hx : 0 < x) : ContinuousAt w x :=
    Complex.continuous_ofReal.continuousAt.mul (hk x hx)
  have i1 : Integrable (fun x => k x * deriv flux x) :=
    spectralPositiveCompactProduct_integrable k (deriv flux) hk hflux'.continuous hcflux.deriv hpflux'
  have i2 : Integrable (fun x => deriv k x * flux x) :=
    spectralPositiveCompactProduct_integrable (deriv k) flux hk' hflux.continuous hcflux hpflux
  have i0 : Integrable (fun x => k x * flux x) :=
    spectralPositiveCompactProduct_integrable k flux hk hflux.continuous hcflux hpflux
  have i3 : Integrable (fun x => v x * deriv g x) :=
    spectralPositiveCompactProduct_integrable v (deriv g) hv hg'.continuous hc.deriv hpg'
  have i4 : Integrable (fun x => v' x * g x) :=
    spectralPositiveCompactProduct_integrable v' g hv' hg.continuous hc hp
  have i5 : Integrable (fun x => w x * g x) :=
    spectralPositiveCompactProduct_integrable w g hw hg.continuous hc hp
  have ivg : Integrable (fun x => v x * g x) :=
    spectralPositiveCompactProduct_integrable v g hv hg.continuous hc hp
  have hfirst : (∫ x : ℝ, k x * deriv flux x) = -∫ x : ℝ, deriv k x * flux x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x hx => (schlafliBesselK_hasDerivAt ν x (hpflux hx)).differentiableAt.hasDerivAt)
      (fun x _ => (hflux.differentiable (by norm_num) x).hasDerivAt) i1 i2 i0
  have hsecond : (∫ x : ℝ, v x * deriv g x) = -∫ x : ℝ, v' x * g x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x hx => spectralKFlux_hasDerivAt ν (hp hx))
      (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt) i3 i4 ivg
  have heq : (∫ x : ℝ, deriv k x * flux x) = ∫ x : ℝ, v x * deriv g x := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [flux, spectralKLCompactFlux, v, spectralKFlux, k]
    ring
  have hzero : g 0 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => lt_irrefl (0 : ℝ) (show (0 : ℝ) < 0 from hp h))
  have hfluxzero : deriv flux 0 = 0 := deriv_of_notMem_tsupport
    (fun h => lt_irrefl (0 : ℝ) (show (0 : ℝ) < 0 from hpflux h))
  have hfun : (fun x => spectralKLCompactOrderIntegrand (spectralKLPhysicalOperator g) ν x) =
      (fun x => -(k x * deriv flux x) + w x * g x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv,
        spectralKLPhysicalOperator, hfluxzero, w, flux]
    · dsimp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv,
        spectralKLPhysicalOperator, k, flux, w]
      field_simp [Complex.ofReal_ne_zero.mpr hx]
  have hsplit : (∫ x : ℝ, -(k x * deriv flux x) + w x * g x) =
      -(∫ x : ℝ, k x * deriv flux x) + ∫ x : ℝ, w x * g x := by
    have h := integral_add i1.neg i5
    simpa only [Pi.neg_apply, integral_neg] using h
  have hsplit' : (∫ x : ℝ, -(v' x * g x) + w x * g x) =
      -(∫ x : ℝ, v' x * g x) + ∫ x : ℝ, w x * g x := by
    have h := integral_add i4.neg i5
    simpa only [Pi.neg_apply, integral_neg] using h
  have hfinal : (fun x => -(v' x * g x) + w x * g x) =
      (fun x => -(ν ^ 2) * spectralKLCompactOrderIntegrand g ν x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [v', w, spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hzero]
    · dsimp [v', w, k, spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv]
      field_simp [Complex.ofReal_ne_zero.mpr hx]
      ring
  calc
    _ = -(∫ x : ℝ, v' x * g x) + ∫ x : ℝ, w x * g x := by
      rw [spectralKLCompactOrderTransform, hfun, hsplit, hfirst, neg_neg, heq, hsecond]
    _ = ∫ x : ℝ, -(v' x * g x) + w x * g x := hsplit'.symm
    _ = _ := by rw [hfinal, integral_const_mul]; rfl

end
end ArtinMatthews
