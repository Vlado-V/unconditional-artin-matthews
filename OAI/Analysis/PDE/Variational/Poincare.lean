module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Green.BoxGreen
public import OAI.Analysis.PDE.Green.GreenReal


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete cell Poincaré inequality.  Only one transverse zero trace is
needed; no artificial boundary condition is imposed on the periodic faces. -/

open Set _root_.MeasureTheory
open scoped ContDiff
noncomputable section

namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Green

variable {m : ℕ}

theorem cell_weighted_energy_identity
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b) (j : Fin (m + 1))
    {u : (Fin (m + 1) → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      u (j.insertNth (b j) y) = 0) :
    (∫ x in Icc a b, u x ^ 2) =
      -(∫ x in Icc a b, 2 * u x * (x j - a j) * fderiv ℝ u x (Pi.single j 1)) := by
  let F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ :=
    fun i x ↦ if i = j then x j - a j else 0
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    by_cases hi : i = j
    · subst i
      have h : ContDiff ℝ 1 (fun x : Fin (m + 1) → ℝ ↦ x j - a j) :=
        (contDiff_apply ℝ ℝ j).sub contDiff_const
      simpa [F] using h
    · simpa only [F, ite_eq_right hi] using (contDiff_const : ContDiff ℝ 1 (fun _ :
        (Fin (m + 1) → ℝ) ↦ (0 : ℝ)))
  have hdF (x : Fin (m + 1) → ℝ) :
      (∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 1 := by
    have hj : HasFDerivAt (F j)
        (ContinuousLinearMap.proj j : (Fin (m + 1) → ℝ) →L[ℝ] ℝ) x := by
      simpa [F] using
        (ContinuousLinearMap.proj j : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.sub_const (a j)
    rw [Finset.sum_eq_single j]
    · rw [hj.fderiv]
      simp
    · intro i _ hij
      simp [F, hij]
    · simp
  have hdu (x : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun y ↦ u y ^ 2) x (Pi.single j 1) =
        2 * u x * fderiv ℝ u x (Pi.single j 1) := by
    rw [((hu.differentiable one_ne_zero x).hasFDerivAt.pow 2).fderiv]
    simp
  have hid := OAI.Analysis.PDE.Green.integral_product_divergence_box a b hab F hF (hu.pow 2) (by
    intro i y hy
    by_cases hij : i = j
    · subst i
      simp [F, hzero y hy]
    · simp [F, hij])
  simp only [hdF, mul_one] at hid
  convert hid using 2
  congr 1
  funext x
  simp only [F, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hdu]
  ring

theorem cell_poincare_directional
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b) (j : Fin (m + 1))
    {u : (Fin (m + 1) → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      u (j.insertNth (b j) y) = 0) :
    (∫ x in Icc a b, u x ^ 2) ≤
      4 * (b j - a j) ^ 2 * (∫ x in Icc a b, (fderiv ℝ u x (Pi.single j 1)) ^ 2) := by
  let d := fun x ↦ fderiv ℝ u x (Pi.single j 1)
  have hd : Continuous d := OAI.Analysis.PDE.Green.continuous_directional hu (Pi.single j 1)
  have hsq : IntegrableOn (fun x ↦ u x ^ 2) (Icc a b) :=
    (hu.continuous.pow 2).integrableOn_Icc
  have hdsq : IntegrableOn (fun x ↦ d x ^ 2) (Icc a b) := (hd.pow 2).integrableOn_Icc
  have hw : IntegrableOn (fun x ↦ -(2 * u x * (x j - a j) * d x)) (Icc a b) :=
    ((((continuous_const.mul hu.continuous).mul ((continuous_apply j).sub continuous_const)).mul
      hd).neg).integrableOn_Icc
  have hbnd (x : Fin (m + 1) → ℝ) (hx : x ∈ Icc a b) :
      -(2 * u x * (x j - a j) * d x) ≤
        (1 / 2 : ℝ) * u x ^ 2 + 2 * (b j - a j) ^ 2 * d x ^ 2 := by
    have ht : 0 ≤ x j - a j := sub_nonneg.mpr (hx.1 j)
    have htL : x j - a j ≤ b j - a j := sub_le_sub_right (hx.2 j) (a j)
    have hL : (x j - a j) ^ 2 ≤ (b j - a j) ^ 2 :=
      pow_le_pow_left₀ ht htL 2
    have hs := sq_nonneg (u x + 2 * (x j - a j) * d x)
    have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg (d x))
    nlinarith
  have hi := setIntegral_mono_on hw
    ((hsq.const_mul (1 / 2 : ℝ)).add (hdsq.const_mul (2 * (b j - a j) ^ 2)))
    measurableSet_Icc hbnd
  simp only [Pi.add_apply] at hi
  rw [integral_neg, ← cell_weighted_energy_identity a b hab j hu hzero,
    integral_add (hsq.const_mul (1 / 2 : ℝ))
      (hdsq.const_mul (2 * (b j - a j) ^ 2)), integral_const_mul, integral_const_mul] at hi
  change (∫ x in Icc a b, u x ^ 2) ≤
    4 * (b j - a j) ^ 2 * (∫ x in Icc a b, d x ^ 2)
  linarith

end OAI.Analysis.PDE.Variational
