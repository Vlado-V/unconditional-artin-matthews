module

public import ArtinMatthews.MarkedPhysicalMemoryHistoryIndex
public import ArtinMatthews.MarkedMemoryStageWeights
public import ArtinMatthews.MarkedMemoryStageVertices
public import ArtinMatthews.MarkedPhysicalMemoryLocalCoefficient
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact alternating physical coefficient on an actual history. All
physical V factors and both slot averages are present; the odd kernel
is the reflected conjugate Schwartz cutoff with conjugate detector. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

def markedMemoryAlternatingPsi (ψ : SchwartzMap ℝ ℂ) (k : ℕ) : SchwartzMap ℝ ℂ :=
  if k%2=0 then ψ else markedRawEdgeAdjointCutoff ψ

def markedMemoryAlternatingEta (η : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  if k%2=0 then η else fun u => star (η u)

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  {s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R)}
  (H : MarkedMemoryChronologicalHistory hZ n s)

theorem markedPhysicalMemoryHistory_coefficient
    (hs : s.1.1=(1,0))
    (hd : ∀ v,MarkedRawActiveDistinct (markedMemoryHistoryVertexState hZ H v).2.1) :
    markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
      (markedPhysicalMemoryHistoryIndex P hP hZ H)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        markedMemoryStageResidualProduct hZ (markedMemoryAlternatingPsi ψ) (markedMemoryAlternatingEta η)
          d₀ Y Q (fun _ _ => 1) n 0 H := by
  rw [markedMemoryStageResidualProduct_vertices]
  unfold markedPhysicalCoordinateIndexCoefficient markedPhysicalCoordinateLabelKernel
  calc
    _ = ∏ v : Fin n,((∏ j,(V j)⁻¹:ℝ):ℂ)*
        markedMemoryEdgeResidual hZ (markedMemoryAlternatingPsi ψ v.val)
          (markedMemoryAlternatingEta η v.val) d₀ Y Q (fun _ => 1)
          (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
            (markedMemoryHistoryVertexGhost hZ H v.castSucc))
          (markedMemoryHistoryVertexEdge hZ H v) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [markedPhysicalMemoryHistoryIndex_path P hP hZ H hs,
        markedPhysicalMemoryHistoryIndex_path P hP hZ H hs]
      have he := markedMemoryHistoryVertexEdge_target hZ H v
      have ht : MarkedRawActiveDistinct
          (markedMemoryEdgeChoiceTarget hZ _ (markedMemoryHistoryVertexEdge hZ H v)).2.1 := by
        rw [he]
        exact hd v.succ
      have hh := markedPhysicalCoordinateLabelCopy_memory hZ V ψ η d₀ Y Q P hP v.val
        (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H v.castSucc))
        (markedMemoryHistoryVertexEdge hZ H v) (hd v.castSucc) ht
      rw [he] at hh
      have hga : (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H v.castSucc)).2.1=
          (markedMemoryHistoryVertexState hZ H v.castSucc).2.1 := rfl
      have hgp : (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H v.castSucc)).1.1=
          (markedMemoryHistoryVertexState hZ H v.castSucc).1.1 := rfl
      rw [hga,hgp] at hh
      by_cases hv : v.val%2=0
      · simpa only [markedPhysicalMemoryHistoryIndex,markedMemoryAlternatingPsi,
          markedMemoryAlternatingEta,hv,ite_true] using hh
      · simpa only [markedPhysicalMemoryHistoryIndex,markedMemoryAlternatingPsi,
          markedMemoryAlternatingEta,hv,ite_false] using hh
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Nat.zero_add]

theorem markedPhysicalMemoryHistory_supported_coefficient
    (hs : s.1.1=(1,0)) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ H) :
    markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
      (markedPhysicalMemoryHistoryIndex P hP hZ H)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        markedMemoryStageResidualProduct hZ (markedMemoryAlternatingPsi ψ) (markedMemoryAlternatingEta η)
          d₀ Y Q (fun _ _ => 1) n 0 H := by
  apply markedPhysicalMemoryHistory_coefficient P hP hZ V ψ η d₀ Y Q H hs
  intro v
  exact (markedPhysicalMarkingEquiv_distinct P hP (pads+1) _).mp
    (markedPhysicalMemoryHistoryIndex_distinct P hP hZ H hempty hd v)

end
end ArtinMatthews
