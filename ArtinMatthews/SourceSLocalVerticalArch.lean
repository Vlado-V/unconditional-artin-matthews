module

public import ArtinMatthews.SourceSLocalVerticalProduct
public import ArtinMatthews.SourceComplexMellinRapid
public import ArtinMatthews.SourceSLocalVerticalLine
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Actual complex-place Mellin transforms supply the retained archimedean estimates. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical SchwartzMap
noncomputable section

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
variable (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
variable (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

variable (ga : InfinitePlace K → 𝓢(ℂ, ℂ))
variable (hga : ∀ w : {w : InfinitePlace K // w ≠ v}, ∀ s : ℂ, 0 < s.re →
  sourceSheetArchMellin μarch garch w.val s = sourceComplexMellin (ga w.val) s)

include hga in
theorem sourceSLocalMellinProduct_vertical_rapid_of_archMellin (n : ℕ) (g : 𝓢(ℂ, ℂ))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hf : ∀ p : S, ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi → ‖sourceSheetFiniteMellin S μf gf p s‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceSLocalMellinProduct S v μarch μf garch gf g s‖ ≤ C := by
  apply sourceSLocalMellinProduct_vertical_rapid S v μarch μf garch gf n g lo hi hlo _ hf
  intro w
  obtain ⟨A, hA, h⟩ := sourceComplexMellin_vertical_rapid 0 (ga w.val) lo hi hlo
  refine ⟨A, hA, fun s hl hh => ?_⟩
  rw [hga w s (hlo.trans_le hl)]
  simpa only [pow_zero, one_mul] using h s hl hh

include hga in
theorem sourceSLocalMellinProduct_verticalIntegrable_of_archMellin (g : 𝓢(ℂ, ℂ))
    (σ : ℝ) (hσ : 0 < σ)
    (hf : ∀ p : S, ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I)‖ ≤ B)
    (hf_cont : ∀ p : S,
      Continuous (fun t : ℝ => sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I))) :
    Complex.VerticalIntegrable (sourceSLocalMellinProduct S v μarch μf garch gf g) σ := by
  have hr (t : ℝ) : ((σ : ℂ) + t * Complex.I).re = σ := by simp [Complex.mul_re]
  have he (w : {w : InfinitePlace K // w ≠ v}) :
      (fun t : ℝ => sourceSheetArchMellin μarch garch w.val ((σ : ℂ) + t * Complex.I)) =
      (fun t : ℝ => sourceComplexMellin (ga w.val) ((σ : ℂ) + t * Complex.I)) :=
    funext fun t => hga w _ ((hr t).symm ▸ hσ)
  apply sourceSLocalMellinProduct_verticalIntegrable S v μarch μf garch gf g σ hσ _ hf _ hf_cont
  · intro w
    obtain ⟨A, hA, h⟩ := sourceComplexMellin_vertical_rapid 0 (ga w.val) σ σ hσ
    refine ⟨A, hA, fun t => ?_⟩
    rw [congrFun (he w) t]
    simpa only [pow_zero, one_mul] using h ((σ : ℂ) + t * Complex.I) (hr t).ge (hr t).le
  · intro w
    rw [he w]
    exact continuous_sourceComplexMellin_vertical (ga w.val) σ hσ

end
end ArtinMatthews.SourcePhysical
