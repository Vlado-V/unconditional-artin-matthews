module

public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein
public import ArtinMatthews.SourceKPCuspNativeUpperPoint
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceKPCuspFourierCell
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
import ArtinMatthews.SourceKPCuspSobolev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen SourceArchJacquet Matrix
open OAI.CubicEisenstein
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspArchHeight (y : V → ℝ) : ℝ := ∏ v, (y v)^2

def sourceKPCuspArchPower (s : ℂ) (y : V → ℝ) : ℂ :=
  Complex.exp ((s+1/2) * (Real.log (sourceKPCuspArchHeight K y) : ℂ))

theorem sourceKPCuspArchHeight_pos (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    0 < sourceKPCuspArchHeight K y := Finset.prod_pos (fun v _ => pow_pos (hy v) _)

theorem sourceKPCuspArchHeight_continuous : Continuous (sourceKPCuspArchHeight K) := by
  unfold sourceKPCuspArchHeight
  fun_prop

theorem sourceKPCuspHeightSection_spherical (s : ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceArchSphericalProduct K hζ s (sourceKPCuspHeightSection K hζ y hy) =
      sourceKPCuspArchPower K s y := by
  change sourceArchSphericalProduct K hζ s
    (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ
      (fun v => WithLp.toLp 2 ![(0:ℝ),0,y v]) (fun v => hy v))) = _
  rw [sourceArchSphericalProduct_upperHalfspace K hζ s
    (fun v => WithLp.toLp 2 ![(0:ℝ),0,y v]) (fun v => hy v)]
  unfold sourceArchCoordinateProduct sourceArchCoordinateProfile
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    positiveHeightPower, logRatioPower, Real.log_one, sub_zero]
  rw [← Complex.exp_sum]
  unfold sourceKPCuspArchPower
  congr 1
  have hlog : (Real.log (sourceKPCuspArchHeight K y) : ℂ) =
      ∑ v : V, (2 : ℂ) * (Real.log (y v) : ℂ) := by
    unfold sourceKPCuspArchHeight
    rw [Real.log_prod (fun v _ => pow_ne_zero 2 (hy v).ne')]
    simp only [Real.log_pow, Nat.cast_ofNat]
    push_cast
    rfl
  rw [hlog, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem sourceKPCuspArchPower_residue (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspArchPower K (-(1/6:ℂ)) y =
      ((sourceKPCuspArchHeight K y ^ (1/3:ℝ) : ℝ) : ℂ) := by
  unfold sourceKPCuspArchPower
  rw [Real.rpow_def_of_pos (sourceKPCuspArchHeight_pos K y hy), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem sourceKPCuspHeightSection_scalar (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPAdelicCompactScalar K hζ s (sourceKPCuspHeightSection K hζ y hy,qf) =
      sourceKPCuspArchPower K s y * sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  rw [sourceArchCompactScalar_factor, sourceKPCuspHeightSection_spherical]

theorem sourceKPCuspHeightSection_intertwiner {s : ℂ} (hs : 0 < s.re)
    (qf : SourceKPFiniteAdeleProjective K hζ) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPAdelicTraceIntertwiner K hζ s (sourceKPCuspHeightSection K hζ y hy,qf) =
      sourceKPCuspArchPower K (-s) y * sourceKPAdelicTraceIntertwiner K hζ s (1,qf) := by
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs,
    sourceKPAdelicTraceIntertwiner_at_finite K hζ hs]
  simp only [Prod.fst, Prod.snd, sourceKPCuspHeightSection_spherical]
  ring

variable (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
local instance : MeasurableSpace (SourceKPCuspPrincipalQuotient K d) := borel _
local instance : BorelSpace (SourceKPCuspPrincipalQuotient K d) := ⟨rfl⟩
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)

include hperiod in
theorem sourceKPCuspNativeEisenstein_mean {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    (∫ x : I → ℝ, sourceKPAutomorphicCompactEisenstein K hζ s
      (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPCuspProductCoordinates K hζ d hd (x,y))) ∂unitTorusUnitCellMeasure I) =
      sourceKPAdelicCompactScalar K hζ s (sourceKPCuspHeightSection K hζ y hy,qf) +
        sourceKPAdelicTraceIntertwiner K hζ s (sourceKPCuspHeightSection K hζ y hy,qf) := by
  let g := (sourceKPCuspHeightSection K hζ y hy,qf)
  let hp := sourceKPCuspFinitePeriod_arch_change K hζ d qf hperiod g.1
  have hcell := sourceKPCuspPrincipalFrequency_integral_unitCell K hζ d hd (0:K)
    ⟨0,by simp⟩ (sourceKPCuspEisensteinCell K hζ d g hp s)
    (sourceKPCuspEisensteinCell_continuous K hζ d g hp hs).measurable
  simp only [map_zero, zero_mul, AddChar.map_zero_eq_one, star_one, one_mul,
    sourceKPCuspEisensteinCell_mk] at hcell
  calc
    _ = ∫ x : I → ℝ, sourceKPAdelicCompactEisenstein K hζ s
        (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x)*g)
        ∂unitTorusUnitCellMeasure I := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sourceKPCuspNativeUpperPoint_compact, sourceKPAutomorphicCompactEisenstein_adelic]
    _ = _ := hcell.symm.trans (sourceKPAdelicCompactEisenstein_traceConstantTerm K hζ hs g)

end
end ArtinMatthews
