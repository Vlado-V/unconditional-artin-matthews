module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Regularity
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
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
public import OAI.Analysis.PDE.Weak.Elliptic.Product


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Smooth coefficient multiplication preserves every finite order of
actual local weak L² regularity. -/
theorem WeakRegularity.operator_mul
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → E →L[ℝ] F) (hA : SmoothBounded A)
    {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M) :
    WeakRegularity Ω k
      (fieldMultiplierCLM A hA.1.continuous.aestronglyMeasurable (Eventually.of_forall hM) u) := by
  induction k generalizing A u M with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    have hAi : SmoothBounded (coordinateDerivative A i) := hA.partial i
    obtain ⟨D, hD⟩ := hAi.bound
    let ag := fieldMultiplierCLM A hA.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hM) g
    let du := fieldMultiplierCLM (coordinateDerivative A i) hAi.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hD) u
    refine ⟨ag + du, ?_, ?_⟩
    · have hr := hd.operator_apply volume A (hA.1.of_le (by simp)) u g
      apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hr
      · filter_upwards [fieldMultiplierCLM_ae A hA.1.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) u] with x hx
        exact fun _ ↦ hx.symm
      · filter_upwards [fieldMultiplierCLM_ae A hA.1.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) g,
          fieldMultiplierCLM_ae (coordinateDerivative A i) hAi.1.continuous.aestronglyMeasurable
            (Eventually.of_forall hD) u, Lp.coeFn_add ag du] with x hx hy hz
        intro _
        rw [hz]
        change A x (g x) + fderiv ℝ A x (Pi.single i 1) (u x) = ag x + du x
        rw [hx, hy]
        rfl
    · exact (ih (u := g) hg A hA hM).add
        (ih (u := u) hu.pred (coordinateDerivative A i) hAi hD)

end OAI.Analysis.PDE.Weak
