module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.Tests
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
public import OAI.Analysis.PDE.Variational.WeakGradient


set_option backward.privateInPublic true
@[expose] public section

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

def cellInterior (a b : CellCoordinates m) : Set (CellCoordinates m) :=
  {x | ∀ i, a i < x i ∧ x i < b i}

def cellZeroExtension {H : Type*} [NormedAddCommGroup H]
    (a b : CellCoordinates m) (f : Lp H 2 (volume.restrict (Icc a b))) :
    CellCoordinates m → H := (Icc a b).indicator f

theorem memLp_cellZeroExtension {H : Type*} [NormedAddCommGroup H]
    (a b : CellCoordinates m) (f : Lp H 2 (volume.restrict (Icc a b))) :
    MemLp (cellZeroExtension a b f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr (Lp.memLp f)

theorem cellInterior_test_face_zero (a b : CellCoordinates m)
    {φ : CellCoordinates m → ℝ} (hφ : tsupport φ ⊆ cellInterior a b)
    (j : Fin (m+1)) (y : Fin m → ℝ) :
    φ (j.insertNth (a j) y) = 0 ∧ φ (j.insertNth (b j) y) = 0 := by
  constructor
  · by_contra hx
    have h := hφ (subset_tsupport _ hx) j
    simpa only [Fin.insertNth_apply_same, lt_self_iff_false] using h.1
  · by_contra hx
    have h := hφ (subset_tsupport _ hx) j
    simpa only [Fin.insertNth_apply_same, lt_self_iff_false] using h.2

theorem integral_mul_cellZeroExtension (a b : CellCoordinates m)
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) (g : CellCoordinates m → ℝ) :
    (∫ x, g x * cellZeroExtension a b f x) = ∫ x in Icc a b, g x * f x := by
  have h : (fun x ↦ g x * cellZeroExtension a b f x) =
      (Icc a b).indicator (fun x ↦ g x * f x) := by
    funext x
    by_cases hx : x ∈ Icc a b <;> simp [cellZeroExtension, hx]
  rw [h, integral_indicator measurableSet_Icc]

theorem integral_coordinate_cellZeroExtension (a b : CellCoordinates m)
    (f : Lp (CellVectors m) 2 (volume.restrict (Icc a b)))
    (g : CellCoordinates m → ℝ) (j : Fin (m+1)) :
    (∫ x, g x * (cellZeroExtension a b f x) j) = ∫ x in Icc a b, g x * (f x) j := by
  have h : (fun x ↦ g x * (cellZeroExtension a b f x) j) =
      (Icc a b).indicator (fun x ↦ g x * (f x) j) := by
    funext x
    by_cases hx : x ∈ Icc a b <;> simp [cellZeroExtension, hx]
  rw [h, integral_indicator measurableSet_Icc]

/-- The completed test-gradient pair is an actual weakly differentiable L² function
on the open cell. The displayed functions are zero-extended to the full coordinate space. -/
theorem cellZeroExtension_weak_derivative (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hΩ : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : PeriodicH10 a b Ω P) (j : Fin (m+1)) {φ : CellCoordinates m → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : tsupport φ ⊆ cellInterior a b) :
    (∫ x, fderiv ℝ φ x (Pi.single j 1) * cellZeroExtension a b (periodicValue a b Ω P u) x) =
      -(∫ x, φ x * (cellZeroExtension a b u.val x) j) := by
  rw [integral_mul_cellZeroExtension, integral_coordinate_cellZeroExtension]
  exact periodicValue_weak_derivative a b hab Ω P k hΩ u j hφ
    (fun y _ ↦ cellInterior_test_face_zero a b hs j y)

end OAI.Analysis.PDE.Variational
