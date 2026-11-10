module

public import ArtinMatthews.SourceKPCompactTestBumps
public import ArtinMatthews.SourceKPAutomorphicExhaustion
public import ArtinMatthews.SourceKPExteriorRadialCore
public import ArtinMatthews.SourceKPCompactExhaustionEnergy
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

/-! Sine and cosine cutoffs on the literal compact automorphic test core. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "P" => ProductSpace (InfinitePlace K)

def sourceKPCompactExhaustionAngle (n : ℕ) (y : Y) : ℝ :=
  (Real.pi/2)*(1-sourceKPAutomorphicExhaustionCutoff K hζ n y)

theorem sourceKPCompactExhaustionAngle_continuous (n : ℕ) :
    Continuous (sourceKPCompactExhaustionAngle K hζ n) :=
  continuous_const.mul (continuous_const.sub (sourceKPAutomorphicExhaustionCutoff_continuous K hζ n))

theorem sourceKPCompactExhaustionTrig_chart_contDiff (n : ℕ)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ
      (fun y => (a (sourceKPCompactExhaustionAngle K hζ n y) : ℂ)) b) Ω := by
  let u : P → ℝ := fun x => (sourceKPCompactChartPullback K hζ
    (sourceKPCompactExhaustionC2 K hζ n).val b x).re
  have hu : ContDiffOn ℝ 2 u Ω := Complex.reCLM.contDiff.comp_contDiffOn
    ((sourceKPCompactExhaustionC2 K hζ n).prop.2.2 b)
  have hangle : ContDiffOn ℝ 2 (fun x => (Real.pi/2)*(1-u x)) Ω :=
    contDiffOn_const.mul (contDiffOn_const.sub hu)
  have h := Complex.ofRealCLM.contDiff.comp_contDiffOn (ha.comp_contDiffOn hangle)
  apply h.congr
  intro x hx
  simp only [sourceKPCompactChartPullback,ite_eq_left hx,sourceKPCompactExhaustionAngle,u,
    sourceKPCompactExhaustionC2_apply,Function.comp_apply,Complex.ofRealCLM_apply,Complex.ofReal_re]

def sourceKPCompactExhaustionTrigMul (n : ℕ) (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (f : T) : T :=
  sourceKPCompactCoreMul K hζ f (fun y => (a (sourceKPCompactExhaustionAngle K hζ n y) : ℂ))
    (Complex.continuous_ofReal.comp (ha.continuous.comp (sourceKPCompactExhaustionAngle_continuous K hζ n)))
    (sourceKPCompactExhaustionTrig_chart_contDiff K hζ n a ha)

def sourceKPCompactExhaustionCos (n : ℕ) (f : T) : T :=
  sourceKPCompactExhaustionTrigMul K hζ n Real.cos Real.contDiff_cos f

def sourceKPCompactExhaustionSin (n : ℕ) (f : T) : T :=
  sourceKPCompactExhaustionTrigMul K hζ n Real.sin Real.contDiff_sin f

theorem sourceKPCompactExhaustionCos_apply (n : ℕ) (f : T) (y : Y) :
    (sourceKPCompactExhaustionCos K hζ n f).val y =
      f.val y * (Real.cos (sourceKPCompactExhaustionAngle K hζ n y) : ℂ) := rfl

theorem sourceKPCompactExhaustionSin_apply (n : ℕ) (f : T) (y : Y) :
    (sourceKPCompactExhaustionSin K hζ n f).val y =
      f.val y * (Real.sin (sourceKPCompactExhaustionAngle K hζ n y) : ℂ) := rfl

theorem sourceKPCompactExhaustionCos_zero (n : ℕ) (f : T) (y : Y)
    (h : sourceKPAutomorphicExhaustionCutoff K hζ n y = 0) :
    (sourceKPCompactExhaustionCos K hζ n f).val y = 0 := by
  rw [sourceKPCompactExhaustionCos_apply,sourceKPCompactExhaustionAngle,h,sub_zero,mul_one,
    Real.cos_pi_div_two,Complex.ofReal_zero,mul_zero]

theorem sourceKPCompactExhaustionSin_tsupport_high (n : ℕ) (f : T) :
    tsupport (sourceKPExteriorCoreLift K hζ (sourceKPCompactExhaustionSin K hζ (n+1) f)) ⊆
      {x | Real.exp ((n : ℝ)+1) < sourceKPAutomorphicOrbitHeight K hζ x} := by
  let g := sourceKPCompactExhaustionSin K hζ (n+1) f
  let q := sourceKPAutomorphicCompactMk K hζ
  have hlocal : tsupport g.val ⊆
      {y | Real.exp ((n : ℝ)+1) < sourceKPAutomorphicCompactOrbitHeight K hζ y} := by
    apply Set.Subset.trans _ (sourceKPCompactExhaustion_complement_tsupport_high K hζ n f.val)
    apply closure_mono
    intro y hy
    change g.val y ≠ 0 at hy
    change ((1 : ℂ) - (sourceKPCompactExhaustionC2 K hζ (n+1)).val y) * f.val y ≠ 0
    intro he
    rcases mul_eq_zero.mp he with hη|hf
    · rw [sourceKPCompactExhaustionC2_apply,sub_eq_zero] at hη
      have hh : sourceKPAutomorphicExhaustionCutoff K hζ (n+1) y = 1 := by
        simpa only [Complex.ofReal_re,Complex.one_re] using (congrArg Complex.re hη).symm
      apply hy
      rw [sourceKPCompactExhaustionSin_apply,sourceKPCompactExhaustionAngle,hh,sub_self,mul_zero,
        Real.sin_zero,Complex.ofReal_zero,mul_zero]
    · apply hy
      rw [sourceKPCompactExhaustionSin_apply,hf,zero_mul]
  have hpre : tsupport (g.val ∘ q) ⊆ q ⁻¹' tsupport g.val := by
    apply closure_minimal _ (isClosed_closure.preimage
      (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous)
    intro x hx
    exact subset_tsupport _ hx
  intro x hx
  have h := hlocal (hpre hx)
  change Real.exp ((n : ℝ)+1) < sourceKPAutomorphicCompactOrbitHeight K hζ (q x) at h
  change Real.exp ((n : ℝ)+1) < sourceKPAutomorphicOrbitHeight K hζ x
  simpa only [q,sourceKPAutomorphicCompactOrbitHeight_mk] using h

end
end ArtinMatthews
