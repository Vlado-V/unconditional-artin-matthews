module

public import ArtinMatthews.MarkedMemoryStageWeights
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
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

/-! The varying-kernel residual is the literal finite product over the
actual chronological edges, with both independent slot probabilities. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryStageResidualProduct_vertices (n offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n offset H=
      ∏ v : Fin n,markedMemoryEdgeResidual hZ (ψStage (offset+v.val)) (ηStage (offset+v.val))
        d₀ Y Q (χ (offset+v.val))
        (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H v.castSucc))
        (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s offset with
  | zero => simp [markedMemoryStageResidualProduct]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change _ * markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n (offset+1) H.2.2=
      _ * ∏ v : Fin n,markedMemoryEdgeResidual hZ (ψStage (offset+(v.val+1)))
        (ηStage (offset+(v.val+1))) d₀ Y Q (χ (offset+(v.val+1)))
        (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H.2.2 v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H.2.2 v.castSucc))
        (markedMemoryHistoryVertexEdge hZ H.2.2 v)
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    rw [show (offset+1)+v.val=offset+(v.val+1) by omega]

end
end ArtinMatthews
