module

public import ArtinMatthews.SourceSLocalVerticalProduct
public import ArtinMatthews.SourceComplexMellinHolomorphic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Continuity and vertical (L^1) for the exact mixed local product. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical SchwartzMap
noncomputable section

theorem continuous_sourceComplexMellin_vertical (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => sourceComplexMellin g ((σ : ℂ) + t * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hs : 0 < ((σ : ℂ) + t * Complex.I).re := by simpa [Complex.mul_re] using hσ
  have hM := (sourceComplexMellin_analyticOnNhd g _ hs).continuousAt
  have ht : Continuous (fun u : ℝ => (σ : ℂ) + u * Complex.I) := by fun_prop
  exact ContinuousAt.comp' (f := fun u : ℝ => (σ : ℂ) + u * Complex.I)
    (g := sourceComplexMellin g) (x := t) hM ht.continuousAt

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
variable (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
variable (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

theorem sourceSLocalMellinProduct_continuous_vertical (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v},
      Continuous (fun t : ℝ => sourceSheetArchMellin μarch garch w.val ((σ : ℂ) + t * Complex.I)))
    (hf : ∀ p : S,
      Continuous (fun t : ℝ => sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I))) :
    Continuous (fun t : ℝ =>
      sourceSLocalMellinProduct S v μarch μf garch gf g ((σ : ℂ) + t * Complex.I)) := by
  let A (w : {w : InfinitePlace K // w ≠ v}) (t : ℝ) :=
    sourceSheetArchMellin μarch garch w.val ((σ : ℂ) + t * Complex.I)
  let B (p : S) (t : ℝ) := sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I)
  have he :
      (fun t : ℝ => sourceSLocalMellinProduct S v μarch μf garch gf g ((σ : ℂ) + t * Complex.I)) =
      (fun t : ℝ => sourceComplexMellin g ((σ : ℂ) + t * Complex.I) *
        ((∏ w, A w t) * ∏ p, B p t)) :=
    funext fun t => sourceSLocalMellinProduct_eq_prod S v μarch μf garch gf g _
  rw [he]
  exact (continuous_sourceComplexMellin_vertical g σ hσ).mul
    ((continuous_finsetProd _ fun w _ => harch w).mul (continuous_finsetProd _ fun p _ => hf p))

/-- Bounded continuous retained factors give an integrable normalized vertical line. -/
theorem sourceSLocalMellinProduct_verticalIntegrable (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v}, ∃ A : ℝ, 0 ≤ A ∧
      ∀ t : ℝ, ‖sourceSheetArchMellin μarch garch w.val ((σ : ℂ) + t * Complex.I)‖ ≤ A)
    (hf : ∀ p : S, ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I)‖ ≤ B)
    (harch_cont : ∀ w : {w : InfinitePlace K // w ≠ v},
      Continuous (fun t : ℝ => sourceSheetArchMellin μarch garch w.val ((σ : ℂ) + t * Complex.I)))
    (hf_cont : ∀ p : S,
      Continuous (fun t : ℝ => sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I))) :
    Complex.VerticalIntegrable (sourceSLocalMellinProduct S v μarch μf garch gf g) σ := by
  have hs (s : ℂ) (hl : σ ≤ s.re) (hh : s.re ≤ σ) : (σ : ℂ) + s.im * Complex.I = s := by
    rw [← le_antisymm hh hl, Complex.re_add_im]
  obtain ⟨C, _, hC⟩ := sourceSLocalMellinProduct_vertical_rapid S v μarch μf garch gf 2 g σ σ hσ
    (fun w => by
      obtain ⟨A, hA, hw⟩ := harch w
      exact ⟨A, hA, fun s hl hh => hs s hl hh ▸ hw s.im⟩)
    (fun p => by
      obtain ⟨B, hB, hp⟩ := hf p
      exact ⟨B, hB, fun s hl hh => hs s hl hh ▸ hp s.im⟩)
  have hc := sourceSLocalMellinProduct_continuous_vertical S v μarch μf garch gf g σ hσ
    harch_cont hf_cont
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num [Module.finrank_self])
  apply (hi.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards with t
  have hr : ((σ : ℂ) + t * Complex.I).re = σ := by simp [Complex.mul_re]
  have hm : ((σ : ℂ) + t * Complex.I).im = t := by simp [Complex.mul_im]
  have h := hC ((σ : ℂ) + t * Complex.I) hr.ge hr.le
  rw [hm] at h
  change ‖sourceSLocalMellinProduct S v μarch μf garch gf g ((σ : ℂ) + t * Complex.I)‖ ≤
    C * (1 + ‖t‖) ^ (-(2 : ℝ))
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv, Real.norm_eq_abs]
  exact (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)).mpr (by rw [mul_comm]; exact h)

end
end ArtinMatthews.SourcePhysical
