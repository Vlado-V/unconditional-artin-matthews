module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.Analysis.PDE.Weak.Elliptic.DifferenceBound
public import OAI.Analysis.PDE.Weak.Elliptic.H1CutoffDerivative
public import OAI.Analysis.PDE.Weak.Elliptic.InteriorEstimate
public import OAI.Analysis.PDE.Weak.Elliptic.InteriorGeometry
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The differentiated local weak solution remains in the actual H¹
completion, not merely in a separately specified weak-derivative space. -/
theorem interior_H1_derivative
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam Λ D K L : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hweak : WeakDivergenceEquation Ω
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L) (hsub : tsupport η ⊆ Ω)
    (j : Fin (m + 1)) :
    ∃ q : H1Pair m, q ∈ H1Zero univ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK p).1 q.1 ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK p).2 q.2 := by
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m) := FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m)
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
  let v : OAI.Analysis.PDE.Variational.CellCoordinates m := Pi.single j 1
  have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
  obtain ⟨s, hs0, hsn, hshift⟩ :=
    exists_small_backward_shifts hs.isCompact hΩ hsub v hv.le
  obtain ⟨J, -, hJ⟩ := exists_cellGradient_derivative_bound hη hs
  have hg : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.cellGradient η) := (contDiff_cellGradient hη).of_le (by simp)
  let E := ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
    4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply exists_H1_derivative_cutoff_of_weighted_difference_bounds p hp η hη hs
    hηM hηK j hs0 hsn (L := L) (J := J) (C := Real.sqrt E)
  · intro n x
    simpa only [hv, mul_one, Real.norm_eq_abs] using
      norm_differenceQuotient_le η (hη.of_le (by simp)) v x (hsn n) (fun t _ ↦ hηL _)
  · intro n x
    simpa only [hv, mul_one] using
      norm_differenceQuotient_le (OAI.Analysis.PDE.Variational.cellGradient η) hg v x (hsn n) (fun t _ ↦ hJ _)
  · intro n
    have hAD : ∀ x, ‖differenceQuotient v (s n) A x‖ ≤ D := by
      intro x
      simpa only [hv, mul_one] using norm_differenceQuotient_le A hA v x (hsn n)
        (fun t _ ↦ hDA _)
    have henergy := interior_difference_energy A hA.continuous hlam hΛ hD hK hAM hell
      p hp f hweak η hη hηM hηK j (hsn n) hAD hsub (hshift n)
    change ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume v (s n) p.2)‖ ^ 2 ≤ E at henergy
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E,
      norm_nonneg (cutoffL2 η hη.continuous hηM (differenceQuotientL2 volume v (s n) p.2))]

end OAI.Analysis.PDE.Weak
