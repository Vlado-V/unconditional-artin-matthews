module

public import ArtinMatthews.MarkedMemoryActivePathFinite
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryPathCapacityExpansion
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedPhysicalMemoryHistoryIndex
public import ArtinMatthews.MarkedMemoryCappedDecorationSum
public import ArtinMatthews.MarkedPhysicalCappedHistoryIndex
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

/-! Exact finite flattening of the original capped decorated carrier.
The genuine birth-order fibers cancel their original factorials; source
and terminal memories remain the actual empty boundary. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [decJ : DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ} (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (z₀ : ↥(markedPrimitiveCoordinateTube R)) (q : ℝ)

attribute [local irreducible] markedMemoryCappedPathIndependent markedMemoryCappedPathDecoratedAssembly

theorem markedPhysicalCappedDecorated_sum
    (F : MarkedPhysicalCoordinateIndex P (pads+1) n R → ℂ) :
    (∑ a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1),
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a),
        ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
              i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
        F (markedPhysicalMemoryHistoryIndex P hP hZ
          (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i))*
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
          (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i)))=
      ∑ d : {d : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads
        (markedPrimitiveCoordinateTube R) n // d.position 0=z₀},
        (markedMemoryPathCappedChoiceSum hZ d.1 q B:ℂ)*
          ∑ order : Fin n → J → Equiv.Perm (Fin pads),
            F (markedPhysicalActivePathIndex P hP d.1 order)*
              if d.1.position (Fin.last n)=z₀ then 1 else 0 := by
  cases Subsingleton.elim decJ (Classical.decEq J)
  let G := fun x : (Σ a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1),
      MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) =>
    ((markedMemoryPathPrimeChoiceWeight hZ x.2.1.path q x.2.1.choices /
      markedMemoryIndependentBirthFactorials hZ
        (markedMemoryCappedPathIndependent (B := B) hZ x.2.1.path x.2.1.choices
          x.2.1.compatible x.2.1.capacity x.2.2.1):ℝ):ℂ)*
      (F (markedPhysicalActivePathIndex P hP x.2.1.path x.2.2.2)*
        if x.2.1.path.position (Fin.last n)=z₀ then 1 else 0)
  have he : (∑ a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1),
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a),
        ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
              i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
        F (markedPhysicalMemoryHistoryIndex P hP hZ
          (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i))*
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
          (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i)))=
      ∑ x,G x := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    rw [markedPhysicalCappedHistoryIndex_eq P hP hdis,
      markedPhysicalCappedHistory_boundary P hdis]
    dsimp only [G]
    ring
  have hs := markedMemoryCappedSourceRaw_sum (P := fun j => markedRawPrimeBand (P j))
    (pads := pads) (B := B) (n := n) hZ z₀ G
  have hf := markedMemoryCappedRawDecorated_sum (P := fun j => markedRawPrimeBand (P j))
    (pads := pads) (B := B) (n := n) hZ z₀ q
    (fun d order => F (markedPhysicalActivePathIndex P hP d order)*
      if d.position (Fin.last n)=z₀ then 1 else 0)
  exact he.trans (hs.trans hf)

end
end ArtinMatthews
