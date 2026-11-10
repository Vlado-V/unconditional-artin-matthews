module

public import ArtinMatthews.SourceKPCompactCoreGradient
public import ArtinMatthews.SourceKPCompactCoreMass
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import ArtinMatthews.SourceKPCompactEnergyRegularity
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

/-! The intrinsic sesquilinear Dirichlet form on the literal compact scalar core. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace Topology ComplexConjugate ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactCorePairDensity (f g : T) (y : Y) : ℂ :=
  inner ℂ (sourceKPCompactCoreGradientAtLinear K hζ y f) (sourceKPCompactCoreGradientAtLinear K hζ y g)

theorem sourceKPCompactCorePairDensity_polarization (f g : T) (y : Y) :
    sourceKPCompactCorePairDensity K hζ f g y =
      ((sourceKPCompactCoreEnergy K hζ (f+g) y : ℂ) - (sourceKPCompactCoreEnergy K hζ (f-g) y : ℂ) +
        ((sourceKPCompactCoreEnergy K hζ (f-Complex.I • g) y : ℂ) -
          (sourceKPCompactCoreEnergy K hζ (f+Complex.I • g) y : ℂ)) * Complex.I) / 4 := by
  let D := sourceKPCompactCoreGradientAtLinear K hζ y
  have hn (u : T) : ‖D u‖ ^ 2 = sourceKPCompactCoreEnergy K hζ u y :=
    sourceKPCompactCoreGradientAt_norm_sq K hζ u y
  have h := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (D f) (D g)
  change inner ℂ (D f) (D g) = ((‖D f+D g‖ : ℂ)^2 - (‖D f-D g‖ : ℂ)^2 +
    ((‖D f-Complex.I • D g‖ : ℂ)^2 - (‖D f+Complex.I • D g‖ : ℂ)^2)*Complex.I)/4 at h
  change inner ℂ (D f) (D g) = _
  simpa only [← D.map_smul Complex.I g,← D.map_add f g,← D.map_sub f g,
    ← D.map_add f (Complex.I • g),← D.map_sub f (Complex.I • g),← Complex.ofReal_pow,hn] using h

theorem sourceKPCompactCorePairDensity_continuous (f g : T) :
    Continuous (sourceKPCompactCorePairDensity K hζ f g) := by
  have he := funext (sourceKPCompactCorePairDensity_polarization K hζ f g)
  rw [he]
  have H (u : T) : Continuous (fun y => (sourceKPCompactCoreEnergy K hζ u y : ℂ)) :=
    Complex.continuous_ofReal.comp (sourceKPCompactCoreEnergy_continuous K hζ u)
  exact (((H (f+g)).sub (H (f-g))).add
    (((H (f-Complex.I • g)).sub (H (f+Complex.I • g))).mul continuous_const)).div_const _

theorem sourceKPCompactCorePairDensity_integrable (f g : T) :
    Integrable (sourceKPCompactCorePairDensity K hζ f g) μ := by
  rw [funext (sourceKPCompactCorePairDensity_polarization K hζ f g)]
  have H (u : T) : Integrable (fun y => (sourceKPCompactCoreEnergy K hζ u y : ℂ)) μ :=
    (sourceKPCompactCoreEnergy_integrable K hζ u).ofReal
  simpa only [div_eq_mul_inv,Pi.add_apply,Pi.sub_apply] using
    (((H (f+g)).sub (H (f-g))).add
      (((H (f-Complex.I • g)).sub (H (f+Complex.I • g))).mul_const Complex.I)).mul_const ((4 : ℂ)⁻¹)

def sourceKPCompactDirichletCore (f g : T) : ℂ :=
  ∫ y, sourceKPCompactCorePairDensity K hζ f g y ∂μ

theorem sourceKPCompactDirichletCore_add_right (f g h : T) :
    sourceKPCompactDirichletCore K hζ f (g+h) =
      sourceKPCompactDirichletCore K hζ f g + sourceKPCompactDirichletCore K hζ f h := by
  unfold sourceKPCompactDirichletCore
  rw [← integral_add (sourceKPCompactCorePairDensity_integrable K hζ f g)
    (sourceKPCompactCorePairDensity_integrable K hζ f h)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [sourceKPCompactCorePairDensity,map_add,inner_add_right,Pi.add_apply]

theorem sourceKPCompactDirichletCore_smul_right (f g : T) (c : ℂ) :
    sourceKPCompactDirichletCore K hζ f (c • g) = c * sourceKPCompactDirichletCore K hζ f g := by
  unfold sourceKPCompactDirichletCore
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [sourceKPCompactCorePairDensity,map_smul,inner_smul_right]

theorem sourceKPCompactDirichletCore_conj_symm (f g : T) :
    conj (sourceKPCompactDirichletCore K hζ f g) = sourceKPCompactDirichletCore K hζ g f := by
  unfold sourceKPCompactDirichletCore
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun y =>
    inner_conj_symm (sourceKPCompactCoreGradientAtLinear K hζ y g)
      (sourceKPCompactCoreGradientAtLinear K hζ y f)

theorem sourceKPCompactDirichletCore_self (f : T) :
    sourceKPCompactDirichletCore K hζ f f = (∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μ : ℝ) := by
  unfold sourceKPCompactDirichletCore
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    rw [sourceKPCompactCorePairDensity,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow,sourceKPCompactCoreGradientAt_norm_sq]

theorem sourceKPCompactDirichletCore_nonneg (f : T) :
    0 ≤ (sourceKPCompactDirichletCore K hζ f f).re := by
  rw [sourceKPCompactDirichletCore_self,Complex.ofReal_re]
  exact integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f)

theorem sourceKPCompactCoreMass_injective (n : ℕ∞ω) :
    Function.Injective (sourceKPCompactCoreMass K hζ n) := by
  let : MeasureTheory.Measure.IsOpenPosMeasure μ := sourceKPAutomorphicCompactHaar_openPositive K hζ
  intro f g hfg
  apply Subtype.ext
  apply (Continuous.ae_eq_iff_eq μ f.prop.1 g.prop.1).mp
  exact (sourceKPCompactCoreMass_coe K hζ f).symm.trans
    (hfg ▸ sourceKPCompactCoreMass_coe K hζ g)

end
end ArtinMatthews
