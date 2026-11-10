module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.CellL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordinateDerivative (f : OAI.Analysis.PDE.Variational.CellCoordinates m → E) (i : Fin (m + 1)) : OAI.Analysis.PDE.Variational.CellCoordinates m → E :=
  fun x ↦ fderiv ℝ f x (Pi.single i 1)

def iteratedCoordinateDerivative : List (Fin (m + 1)) →
    (OAI.Analysis.PDE.Variational.CellCoordinates m → E) → OAI.Analysis.PDE.Variational.CellCoordinates m → E
  | [], f => f
  | i :: α, f => coordinateDerivative (iteratedCoordinateDerivative α f) i

theorem iteratedCoordinateDerivative_append (α β : List (Fin (m + 1)))
    (f : OAI.Analysis.PDE.Variational.CellCoordinates m → E) :
    iteratedCoordinateDerivative (α ++ β) f =
      iteratedCoordinateDerivative α (iteratedCoordinateDerivative β f) := by
  induction α with
  | nil => rfl
  | cons i α ih => simp only [List.cons_append, iteratedCoordinateDerivative, ih]

theorem contDiff_coordinateDerivative {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : ContDiff ℝ ∞ f) (i : Fin (m + 1)) : ContDiff ℝ ∞ (coordinateDerivative f i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_iteratedCoordinateDerivative {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : ContDiff ℝ ∞ f) (α : List (Fin (m + 1))) :
    ContDiff ℝ ∞ (iteratedCoordinateDerivative α f) := by
  induction α with
  | nil => exact hf
  | cons i α ih => exact contDiff_coordinateDerivative ih i

theorem hasCompactSupport_iteratedCoordinateDerivative {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : HasCompactSupport f) (α : List (Fin (m + 1))) :
    HasCompactSupport (iteratedCoordinateDerivative α f) := by
  induction α with
  | nil => exact hf
  | cons i α ih => exact ih.fderiv_apply ℝ (Pi.single i 1)

def SmoothBounded (f : OAI.Analysis.PDE.Variational.CellCoordinates m → E) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ α : List (Fin (m + 1)), ∃ C : ℝ,
    ∀ x, ‖iteratedCoordinateDerivative α f x‖ ≤ C

theorem SmoothBounded.bound {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hf : SmoothBounded f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := hf.2 []

theorem SmoothBounded.partial {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : SmoothBounded f) (i : Fin (m + 1)) : SmoothBounded (coordinateDerivative f i) := by
  refine ⟨contDiff_coordinateDerivative hf.1 i, ?_⟩
  intro α
  simpa only [iteratedCoordinateDerivative_append, iteratedCoordinateDerivative] using hf.2 (α ++ [i])

theorem smoothBounded_of_hasCompactSupport {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : SmoothBounded f := by
  refine ⟨hf, ?_⟩
  intro α
  obtain ⟨C, hC⟩ := ((hasCompactSupport_iteratedCoordinateDerivative hs α).isCompact_range
    (contDiff_iteratedCoordinateDerivative hf α).continuous).isBounded.exists_norm_le
  exact ⟨C, fun x ↦ hC _ (mem_range_self x)⟩

theorem smoothBounded_const (c : E) : SmoothBounded (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ c) := by
  refine ⟨contDiff_const, ?_⟩
  have hc (α : List (Fin (m + 1))) : ∃ b : E,
      iteratedCoordinateDerivative α (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ c) = fun _ ↦ b := by
    induction α with
    | nil => exact ⟨c, rfl⟩
    | cons i α ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨0, ?_⟩
      simp only [iteratedCoordinateDerivative, hb]
      funext x
      exact congrArg (fun L : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] E ↦ L (Pi.single i 1))
        (hasFDerivAt_const (𝕜 := ℝ) (c := b) x).fderiv
  intro α
  obtain ⟨b, hb⟩ := hc α
  exact ⟨‖b‖, fun x ↦ by rw [hb]⟩

theorem iteratedCoordinateDerivative_add {f g : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (α : List (Fin (m + 1))) :
    iteratedCoordinateDerivative α (f + g) =
      iteratedCoordinateDerivative α f + iteratedCoordinateDerivative α g := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    simp only [iteratedCoordinateDerivative, ih]
    funext x
    exact congrArg (fun L ↦ L (Pi.single i 1))
      (((contDiff_iteratedCoordinateDerivative hf α).differentiable (by simp) x).hasFDerivAt.add
        ((contDiff_iteratedCoordinateDerivative hg α).differentiable (by simp) x).hasFDerivAt).fderiv

theorem SmoothBounded.add {f g : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : SmoothBounded f) (hg : SmoothBounded g) : SmoothBounded (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro α
  obtain ⟨C, hC⟩ := hf.2 α
  obtain ⟨D, hD⟩ := hg.2 α
  refine ⟨C + D, ?_⟩
  intro x
  rw [iteratedCoordinateDerivative_add hf.1 hg.1]
  exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))

end OAI.Analysis.PDE.Weak
