module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.MeasureTheory.Function.L2Space
public import OAI.Analysis.PDE.Weak.Elliptic.L2
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
public import OAI.Analysis.PDE.Weak.Elliptic.Adjoint
public import OAI.Analysis.PDE.Weak.Elliptic.TestLimit
public import OAI.Analysis.PDE.Weak.Elliptic.WeakCompactness


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

def HasWeakDirectionalDerivative (v : X) (u g : X → V) : Prop :=
  ∀ φ : X → V, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ x, inner ℝ (g x) (φ x) ∂μ) = -(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)

omit [SecondCountableTopology X] [CompleteSpace V] [IsLocallyFiniteMeasure μ] in
theorem inner_differenceQuotientL2_toLp (v : X) (h : ℝ) (u : Lp V 2 μ)
    {φ : X → V} (hφ : MemLp φ 2 μ) :
    inner ℝ (differenceQuotientL2 μ v h u) (hφ.toLp φ) =
      -(∫ x, inner ℝ (u x) (differenceQuotient v (-h) φ x) ∂μ) := by
  rw [inner_differenceQuotientL2, differenceQuotientL2_toLp, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [(memLp_differenceQuotient μ v (-h) hφ).coeFn_toLp] with x hx
  rw [hx]

theorem hasWeakDerivative_of_difference_limits (u g : Lp V 2 μ)
    (hu1 : Integrable (u : X → V) μ) (v : X) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0)
    (hlimit : ∀ (w : Lp V 2 μ) (l : ℝ),
      Tendsto (fun n ↦ inner ℝ (differenceQuotientL2 μ v (s n) u) w) atTop (𝓝 l) →
        inner ℝ g w = l) : HasWeakDirectionalDerivative μ v u g := by
  intro φ hφ hφs
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hds : HasCompactSupport (fderiv ℝ φ) := hφs.fderiv (𝕜 := ℝ)
  obtain ⟨M, hM⟩ := (hds.isCompact_range (hφ.continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hM' : ∀ x, ‖fderiv ℝ φ x‖ ≤ M := fun x ↦ hM _ (mem_range_self x)
  have hneg : Tendsto (fun n ↦ -s n) atTop (𝓝 0) := by simpa using hs.neg
  have ht := (tendsto_integral_inner_differenceQuotient μ (u : X → V) φ hu1 hφ v
    hM' hneg (fun n ↦ neg_ne_zero.mpr (hs0 n))).neg
  have he := hlimit (hφ2.toLp φ) (-(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)) (by
    simpa only [inner_differenceQuotientL2_toLp] using ht)
  rw [L2.inner_def] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [hφ2.coeFn_toLp] with x hx
  rw [hx]

/-- A bounded sequence of genuine difference quotients produces a genuine
L² weak derivative.  This is the analytic compactness step in interior H². -/
theorem exists_weakDerivative_of_differenceQuotient_bound (u : Lp V 2 μ)
    (hu1 : Integrable (u : X → V) μ) (v : X) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) {C : ℝ}
    (hC : ∀ n, ‖differenceQuotientL2 μ v (s n) u‖ ≤ C) :
    ∃ g : Lp V 2 μ, ‖g‖ ≤ C ∧ HasWeakDirectionalDerivative μ v u g := by
  obtain ⟨g, hg, hlimit⟩ := exists_weak_limit_preserving_scalar_limits
    (fun n ↦ differenceQuotientL2 μ v (s n) u) hC
  refine ⟨g, hg, ?_⟩
  intro φ hφ hφs
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hds : HasCompactSupport (fderiv ℝ φ) := hφs.fderiv (𝕜 := ℝ)
  obtain ⟨M, hM⟩ := (hds.isCompact_range (hφ.continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hM' : ∀ x, ‖fderiv ℝ φ x‖ ≤ M := fun x ↦ hM _ (mem_range_self x)
  have hneg : Tendsto (fun n ↦ -s n) atTop (𝓝 0) := by simpa using hs.neg
  have ht := (tendsto_integral_inner_differenceQuotient μ (u : X → V) φ hu1 hφ v
    hM' hneg (fun n ↦ neg_ne_zero.mpr (hs0 n))).neg
  have he := hlimit (hφ2.toLp φ) (-(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)) (by
    simpa only [inner_differenceQuotientL2_toLp] using ht)
  rw [L2.inner_def] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [hφ2.coeFn_toLp] with x hx
  rw [hx]

end OAI.Analysis.PDE.Weak
