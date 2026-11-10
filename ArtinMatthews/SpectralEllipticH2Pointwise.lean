module

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import ArtinMatthews.SpectralWeakDerivativeClassical
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Gradient
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative evaluation of the actual local H1/H2 graph through compact cutoffs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectral_local_scalar_cutoff_smooth
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (u η : (Fin 2 → ℝ) → ℝ) (hu : ContDiffOn ℝ ∞ u Ω)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ Ω) :
    ContDiff ℝ ∞ (η*u) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · exact hη.contDiffAt.mul (hu.contDiffAt (hΩ.mem_nhds (hsη hx)))
  · have he : η*u =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.mul_apply,hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

def spectralLpNormFunction {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (u : Lp E 2 μ) : Lp ℝ 2 μ :=
  (Lp.memLp u).norm.toLp (fun x => ‖u x‖)

theorem spectralLpNormFunction_ae {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (u : Lp E 2 μ) :
    spectralLpNormFunction u =ᵐ[μ] fun x => ‖u x‖ := MemLp.coeFn_toLp _

theorem spectralLpNormFunction_norm {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (u : Lp E 2 μ) :
    ‖spectralLpNormFunction u‖ = ‖u‖ := by
  rw [spectralLpNormFunction,Lp.norm_toLp,Lp.norm_def,
    eLpNorm_norm _ (Lp.aestronglyMeasurable u)]

theorem spectralLp_norm_le_three_norms
    {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {μ : Measure X} (f : Lp ℝ 2 μ) (u : Lp E 2 μ) (v : Lp F 2 μ) (w : Lp G 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C*(‖u x‖+‖v x‖+‖w x‖)) :
    ‖f‖ ≤ C*(‖u‖+‖v‖+‖w‖) := by
  let z := spectralLpNormFunction u+spectralLpNormFunction v+spectralLpNormFunction w
  have hz : z =ᵐ[μ] fun x => ‖u x‖+‖v x‖+‖w x‖ := by
    filter_upwards [Lp.coeFn_add (spectralLpNormFunction u+spectralLpNormFunction v)
      (spectralLpNormFunction w),Lp.coeFn_add (spectralLpNormFunction u) (spectralLpNormFunction v),
      spectralLpNormFunction_ae u,spectralLpNormFunction_ae v,spectralLpNormFunction_ae w]
      with x h1 h2 hu hv hw
    change (spectralLpNormFunction u+spectralLpNormFunction v+spectralLpNormFunction w) x = _
    simp only [Pi.add_apply] at h1 h2
    rw [h1,h2,hu,hv,hw]
  have hn : ‖z‖ ≤ ‖u‖+‖v‖+‖w‖ := by
    calc
      ‖z‖ ≤ ‖spectralLpNormFunction u+spectralLpNormFunction v‖+‖spectralLpNormFunction w‖ := norm_add_le _ _
      _ ≤ (‖spectralLpNormFunction u‖+‖spectralLpNormFunction v‖)+‖spectralLpNormFunction w‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [spectralLpNormFunction_norm,spectralLpNormFunction_norm,spectralLpNormFunction_norm]
  have hf : ‖f‖ ≤ C*‖z‖ := Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [hb,hz] with x hx hy
    rw [hy,Real.norm_of_nonneg (add_nonneg (add_nonneg (norm_nonneg (u x))
      (norm_nonneg (v x))) (norm_nonneg (w x)))]
    exact hx)
  exact hf.trans (mul_le_mul_of_nonneg_left hn hC)

theorem spectral_localized_gradient_derivative_classical
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (p : H1Pair 1) (hp : p ∈ H1Zero univ)
    (u : (Fin 2 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηM : ∀ x, |η x| ≤ 1) (hsη : tsupport η ⊆ Ω)
    (g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)))
    (hd : HasWeakDirectionalDerivative volume (Pi.single 1 1)
      (cutoffL2 η hη.continuous hηM p.2) g) :
    ∀ᵐ x ∂volume, g x 0 = coordinateDerivative (η*coordinateDerivative u 0) 1 x := by
  have hg := H1Zero.gradient_eq_of_value_eq hΩ hp u (hu.of_le (by simp)) heq
  let V : (Fin 2 → ℝ) → CellVectors 1 := fun x => η x • cellGradient u x
  have hV : ContDiff ℝ 1 V :=
    ((hη.smul (contDiff_cellGradient hu)).of_le (by simp))
  have heV : cutoffL2 η hη.continuous hηM p.2 =ᵐ[volume] V := by
    filter_upwards [cutoffL2_ae η hη.continuous hηM p.2,hg] with x hx hy
    rw [hx]
    by_cases hn : η x = 0
    · simp only [hn,zero_smul,V]
    · exact congrArg (fun v : CellVectors 1 => η x • v)
        (hy (hsη (subset_tsupport η hn)))
  have he := spectral_weak_vector_derivative_classical_component
    (cutoffL2 η hη.continuous hηM p.2) g 1 0 hd V hV heV
  have hfun : (fun x => V x 0) = η*coordinateDerivative u 0 := by
    funext x
    rfl
  simpa only [hfun,coordinateDerivative] using he

end ArtinMatthews
