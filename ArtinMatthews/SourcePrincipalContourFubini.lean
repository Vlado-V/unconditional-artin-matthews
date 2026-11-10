module

public import ArtinMatthews.SourcePrincipalContourIntegrals
public import OAI.NumberTheory.DirichletL.Detector.Physical
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

/-! Exact normalized contour reordering under the proved absolute integrability. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical
noncomputable section

theorem sourcePrincipalHeight_integral_w_last (f : SourcePoissonHeights → ℂ)
    (h : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ u : ℝ, ∫ y : ℝ, ∫ t : ℝ, f ((t,y),u) := by
  unfold sourcePoissonHeightMeasure at h ⊢
  rw [integral_prod_symm f h]
  apply integral_congr_ae
  filter_upwards [h.prod_left_ae] with u hu
  exact integral_prod_symm (fun p : ℝ × ℝ => f (p,u)) hu

theorem sourcePrincipalHeight_integral_xi_last (f : SourcePoissonHeights → ℂ)
    (h : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ t : ℝ, ∫ y : ℝ, ∫ u : ℝ, f ((t,y),u) := by
  unfold sourcePoissonHeightMeasure at h ⊢
  rw [integral_prod f h, integral_prod _ h.integral_prod_left]

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
variable (X Y Z a b c : ℝ)
local notation "N" => sourcePoissonNormalization
local notation "μ₂" => (Measure.prod (volume : Measure ℝ) (volume : Measure ℝ))

def sourcePrincipalPoissonOuterSlice (u : ℝ) : ℂ :=
  N ^ 2 * ∫ p : ℝ × ℝ, sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c (p,u) ∂μ₂

def sourcePrincipalPoissonResidueOuterSlice (u : ℝ) : ℂ :=
  N * ∫ y : ℝ, sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c (y,u)

theorem sourcePrincipalPoissonIntegral_eq_outer
    (hi : Integrable (sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c)
      sourcePoissonHeightMeasure) :
    sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z a b c =
      N * ∫ u : ℝ, sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z a b c u := by
  unfold sourcePrincipalPoissonIntegral sourcePrincipalPoissonOuterSlice
  unfold sourcePoissonHeightMeasure at hi ⊢
  rw [integral_prod_symm _ hi, integral_const_mul]
  ring

theorem sourcePrincipalPoissonResidueIntegral_eq_outer
    (hi : Integrable (sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c) μ₂) :
    sourcePrincipalPoissonResidueIntegral F hζ S₀ η v X Y Z a c =
      N * ∫ u : ℝ, sourcePrincipalPoissonResidueOuterSlice F hζ S₀ η v X Y Z a c u := by
  unfold sourcePrincipalPoissonResidueIntegral sourcePrincipalPoissonResidueOuterSlice
  rw [integral_prod_symm _ hi, integral_const_mul]
  ring

theorem sourcePrincipalPoissonOuterSlice_integrable
    (hi : Integrable (sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c)
      sourcePoissonHeightMeasure) :
    Integrable (sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z a b c) := by
  unfold sourcePoissonHeightMeasure at hi
  exact hi.integral_prod_right.const_mul (N ^ 2)

theorem sourcePrincipalPoissonResidueOuterSlice_integrable
    (hi : Integrable (sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c) μ₂) :
    Integrable (sourcePrincipalPoissonResidueOuterSlice F hζ S₀ η v X Y Z a c) :=
  hi.integral_prod_right.const_mul N

theorem sourcePrincipalPoissonOuterSlice_eq_w_last (u : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c (p,u)) μ₂) :
    sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z a b c u =
      verticalIntegral c (fun z => verticalIntegral b (fun w =>
        sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (sourcePoissonVertical a u,w,z))) := by
  unfold sourcePrincipalPoissonOuterSlice
  rw [integral_prod_symm _ hi]
  unfold verticalIntegral
  simp_rw [integral_const_mul]
  change N ^ 2 * (∫ y : ℝ, ∫ t : ℝ, sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c ((t,y),u)) =
    N * (N * (∫ y : ℝ, ∫ t : ℝ, sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c ((t,y),u)))
  ring

theorem sourcePrincipalPoissonResidueOuterSlice_eq (u : ℝ) :
    sourcePrincipalPoissonResidueOuterSlice F hζ S₀ η v X Y Z a c u =
      verticalIntegral c (sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z (sourcePoissonVertical a u)) := rfl

end
end ArtinMatthews.SourceEulerAssembly
