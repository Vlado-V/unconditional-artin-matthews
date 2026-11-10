module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.Tests
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
public import OAI.Analysis.PDE.Variational.LaxMilgram


set_option backward.privateInPublic true
@[expose] public section

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem periodic_weak_solution_test (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hΩ : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) (u : PeriodicH10 a b Ω P)
    (hu : ∀ v : PeriodicH10 a b Ω P,
      (∫ x in Icc a b, inner ℝ (v.val x) (A x (u.val x))) =
        ∫ x in Icc a b, f x * periodicValue a b Ω P v x)
    (φ : PeriodicTests Ω P) :
    (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
      ∫ x in Icc a b, f x * φ.val x := by
  have h := hu (periodicTestEmbedding a b Ω P φ)
  rw [periodicValue_test a b hab Ω P k hΩ φ] at h
  have hg : (fun x ↦ testGradientMap a b Ω P φ x) =ᵐ[volume.restrict (Icc a b)]
      cellGradient φ := (memLp_continuous_cell a b
        (continuous_cellGradient (periodicTest_contDiff_one φ))).coeFn_toLp
  have hv : (fun x ↦ testValueMap a b Ω P φ x) =ᵐ[volume.restrict (Icc a b)]
      (φ : CellCoordinates m → ℝ) :=
    (memLp_continuous_cell a b (periodicTest_contDiff φ).continuous).coeFn_toLp
  calc
    _ = ∫ x in Icc a b,
        inner ℝ ((periodicTestEmbedding a b Ω P φ).val x) (A x (u.val x)) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      change inner ℝ _ _ = inner ℝ (testGradientMap a b Ω P φ x) _
      rw [hx]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]

theorem periodic_weak_solution_bound (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hΩ : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M lam : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖ ≤ M) (_ : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ v : CellVectors m,
      lam * ‖v‖^2 ≤ inner ℝ v (A x v))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) (u : PeriodicH10 a b Ω P)
    (hu : ∀ v : PeriodicH10 a b Ω P,
      (∫ x in Icc a b, inner ℝ (v.val x) (A x (u.val x))) =
        ∫ x in Icc a b, f x * periodicValue a b Ω P v x) :
    lam * ‖u‖ ≤ (2 * (b k-a k)) * ‖f‖ := by
  have henergy : lam * ‖u‖^2 ≤ ‖f‖ * ((2 * (b k-a k)) * ‖u‖) := by
    calc
      _ ≤ OAI.Analysis.PDE.Dirichlet.coefficientEnergy A hA hM hAM u.val u.val :=
        OAI.Analysis.PDE.Dirichlet.coefficientEnergy_lower_bound A hA hM hAM hell u.val
      _ = inner ℝ f (periodicValue a b Ω P u) := by
        rw [OAI.Analysis.PDE.Dirichlet.coefficientEnergy_eq_integral, hu u, L2.inner_def]
        congr 1
        funext x
        simp [RCLike.inner_apply, mul_comm]
      _ ≤ ‖f‖ * ‖periodicValue a b Ω P u‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_periodicValue_le a b hab Ω P k hΩ u) (norm_nonneg _)
  by_cases hz : ‖u‖=0
  · rw [hz, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hab k))) (norm_nonneg _)
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz))).mp
    nlinarith [henergy]

/-- Actual smooth-test weak Dirichlet solution with its energy estimate. -/
theorem exists_periodic_weak_solution (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hΩ : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M lam : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖ ≤ M) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ v : CellVectors m,
      lam * ‖v‖^2 ≤ inner ℝ v (A x v))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ∃ u : PeriodicH10 a b Ω P,
      (∀ φ : PeriodicTests Ω P,
        (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
          ∫ x in Icc a b, f x * φ.val x) ∧
      lam * ‖u‖ ≤ (2 * (b k-a k)) * ‖f‖ := by
  obtain ⟨u, hu, _⟩ := exists_unique_periodic_weak_solution a b Ω P A hA hM hAM hlam hell f
  exact ⟨u, periodic_weak_solution_test a b hab Ω P k hΩ A f u hu,
    periodic_weak_solution_bound a b hab Ω P k hΩ A hA hM hAM hlam hell f u hu⟩

end OAI.Analysis.PDE.Variational
