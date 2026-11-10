module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Annulus
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelScale
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cancellation
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.NearField


set_option backward.privateInPublic true
@[expose] public section

/-! The Newtonian Hessian principal value exists for Hölder data. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem tendsto_annular_integral {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (g : E → ℝ) (hg : Measurable g)
    {R : ℝ} (hi : IntegrableOn g (ball 0 R) μ) (hg0 : g 0 = 0) :
    Tendsto (fun ε : ℝ => ∫ y in normAnnulus ε R, g y ∂μ) (𝓝[>] 0)
      (𝓝 (∫ y in ball 0 R, g y ∂μ)) := by
  let F : ℝ → E → ℝ := fun ε => {y : E | ε < ‖y‖}.indicator g
  have hFmeas (ε : ℝ) : Measurable (F ε) :=
    hg.indicator (measurableSet_lt measurable_const continuous_norm.measurable)
  have hFbound (ε : ℝ) (y : E) : ‖F ε y‖ ≤ ‖g y‖ := by
    by_cases hy : ε < ‖y‖ <;> simp [F, hy]
  have hFlim (y : E) : Tendsto (fun ε : ℝ => F ε y) (𝓝[>] 0) (𝓝 (g y)) := by
    by_cases hy : y = 0
    · subst y
      simp [F, Set.indicator, hg0]
    · apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds (norm_pos_iff.mpr hy)).filter_mono nhdsWithin_le_nhds] with ε hε
      simp [F, hε]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.restrict (ball 0 R)) (fun y => ‖g y‖)
    (Eventually.of_forall (fun ε => (hFmeas ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (hFbound ε))) hi.norm
    (Eventually.of_forall hFlim)
  have he (ε : ℝ) : (∫ y in ball 0 R, F ε y ∂μ) = ∫ y in normAnnulus ε R, g y ∂μ := by
    change (∫ y in ball 0 R, {y : E | ε < ‖y‖}.indicator g y ∂μ) = _
    rw [setIntegral_indicator (measurableSet_lt measurable_const continuous_norm.measurable)]
    have hs : ball (0 : E) R ∩ {y : E | ε < ‖y‖} = normAnnulus ε R := by
      ext y
      simp [normAnnulus, and_comm]
    rw [hs]
  simpa only [he] using ht

theorem newtonian_compensation_on_annulus {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : Continuous f) (x v w : EuclideanSpace ℝ (Fin m)) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (∫ y in normAnnulus ε R, compensatedNewtonianEntry f x v w y) =
      ∫ y in normAnnulus ε R, f (x - y) * newtonianEntry m v w y := by
  have hK := integrableOn_newtonianEntry_annulus v w hε R
  have hF : IntegrableOn (fun y => f (x - y) * newtonianEntry m v w y) (normAnnulus ε R) :=
    integrableOn_normAnnulus _ (fun y hy =>
      (hf.continuousAt.comp (continuousAt_const.sub continuousAt_id)).mul
        (contDiffAt_newtonianEntry m v w hy).continuousAt) hε R
  have he : compensatedNewtonianEntry f x v w =
      fun y => f (x - y) * newtonianEntry m v w y - f x * newtonianEntry m v w y := by
    funext y
    simp only [compensatedNewtonianEntry, finrank_euclideanSpace_fin, newtonianEntry, sub_mul]
  rw [he, integral_sub hF (hK.const_mul _), integral_const_mul,
    newtonianEntry_annulus v w hε R, mul_zero, sub_zero]

theorem newtonian_principalValue {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f)
    (x v w : EuclideanSpace ℝ (Fin m)) {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y in normAnnulus ε R,
      f (x - y) * newtonianEntry m v w y) (𝓝[>] 0)
      (𝓝 (∫ y in ball 0 R, compensatedNewtonianEntry f x v w y)) := by
  have hd : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by simpa using hm
  have hi := integrableOn_compensatedNewtonianEntry f x v w hd hf.measurable hH hα hholder volume R
  have ht := tendsto_annular_integral volume (compensatedNewtonianEntry f x v w)
    (measurable_compensatedNewtonianEntry f hf.measurable x v w) hi (by
      simp [compensatedNewtonianEntry])
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact newtonian_compensation_on_annulus f hf x v w hε R

end OAI.Analysis.PDE.Schauder
