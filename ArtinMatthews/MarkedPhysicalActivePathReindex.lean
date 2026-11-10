module

public import ArtinMatthews.MarkedMemoryActivePathFinite
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedPhysicalActivePathIndexInjective
public import ArtinMatthews.MarkedPhysicalCoordinateIndexCopies
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

/-! Genuine finite reindexing of the supported physical coordinate
carrier through active paths and compatible copied orders. Support is
read from the original coefficient; zero terms alone are discarded. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads n R : ℕ}

abbrev MarkedPhysicalInitialPathOrders (z₀ : ↥(markedPrimitiveCoordinateTube R)) :=
  Σ _d : {d : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads
    (markedPrimitiveCoordinateTube R) n // d.position 0=z₀},
      Fin n → J → Equiv.Perm (Fin pads)

instance markedPhysicalInitialPathOrders_fintype (z₀ : ↥(markedPrimitiveCoordinateTube R)) :
    Fintype (MarkedPhysicalInitialPathOrders (P := P) (pads := pads) (n := n) z₀) := by infer_instance

def markedPhysicalInitialPathIndex (z₀ : ↥(markedPrimitiveCoordinateTube R))
    (x : MarkedPhysicalInitialPathOrders (P := P) (pads := pads) (n := n) z₀) :
    MarkedPhysicalCoordinateIndex P (pads+1) n R := markedPhysicalActivePathIndex P hP x.1.1 x.2

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalInitialPathIndex_injective (z₀ : ↥(markedPrimitiveCoordinateTube R))
    (hz₀ : z₀.1=(1,0)) : Function.Injective (markedPhysicalInitialPathIndex (pads := pads) (n := n) P hP z₀) := by
  intro a b h
  have hd := markedPhysicalActivePathIndex_path_injective P hP
    ((congrArg Subtype.val a.1.2).trans hz₀) ((congrArg Subtype.val b.1.2).trans hz₀) h
  have hs : a.1=b.1 := Subtype.ext hd
  cases a with
  | mk a order =>
    cases b with
    | mk b orders =>
      change a=b at hs
      cases hs
      have ho := markedPhysicalActivePathIndex_order_injective P hP h
      cases ho
      rfl

theorem markedPhysicalInitialPathIndex_supported_surjective
    (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (z₀ : ↥(markedPrimitiveCoordinateTube R)) (hz₀ : z₀.1=(1,0)) (hR : 1≤R)
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n R)
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))
    (hc : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0) :
    ∃ x : MarkedPhysicalInitialPathOrders (P := P) (pads := pads) (n := n) z₀,
      markedPhysicalInitialPathIndex P hP z₀ x=i := by
  let d := markedPhysicalCoordinateIndexActivePath P hP V pads ψ η d₀ Y Q i hR ha hc
  have hd : d.position 0=z₀ := Subtype.ext hz₀.symm
  exact ⟨⟨⟨d,hd⟩,markedPhysicalCoordinateIndexOrder P hP V pads ψ η d₀ Y Q i hc hR ha⟩,
    markedPhysicalCoordinateIndexOrder_recovery P hP V pads ψ η d₀ Y Q i hc hR ha⟩

theorem markedPhysicalInitialPathIndex_sum
    (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (z₀ : ↥(markedPrimitiveCoordinateTube R)) (hz₀ : z₀.1=(1,0)) (hR : 1≤R)
    (F : MarkedPhysicalCoordinateIndex P (pads+1) n R → ℂ)
    (hbad : ∀ i,¬(∀ v,MarkedPhysicalMarkingDistinct (i.1 v)) → F i=0)
    (hzero : ∀ i,markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i=0 → F i=0) :
    (∑ i,F i)=∑ x : MarkedPhysicalInitialPathOrders (P := P) (pads := pads) (n := n) z₀,
      F (markedPhysicalInitialPathIndex P hP z₀ x) := by
  let f := markedPhysicalInitialPathIndex (pads := pads) (n := n) P hP z₀
  have hf := markedPhysicalInitialPathIndex_injective (pads := pads) (n := n) P hP z₀ hz₀
  calc
    _ = ∑ i∈Finset.univ.image f,F i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_cases ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v)
      · by_cases hc : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i=0
        · exact hzero i hc
        · obtain ⟨x,hx⟩ := markedPhysicalInitialPathIndex_supported_surjective P hP V ψ η d₀ Y Q z₀ hz₀ hR i ha hc
          exact False.elim (hi (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩))
      · exact hbad i ha
    _ = _ := by rw [Finset.sum_image (fun a _ b _ h => hf h)]

theorem markedPhysicalActivePathIndex_activePath
    (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (d : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads (markedPrimitiveCoordinateTube R) n)
    (order : Fin n → J → Equiv.Perm (Fin pads)) (hd : (d.position 0).1=(1,0)) (hR : 1≤R)
    (ha : ∀ v,MarkedPhysicalMarkingDistinct ((markedPhysicalActivePathIndex P hP d order).1 v))
    (hc : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
      (markedPhysicalActivePathIndex P hP d order)≠0) :
    markedPhysicalCoordinateIndexActivePath P hP V pads ψ η d₀ Y Q
      (markedPhysicalActivePathIndex P hP d order) hR ha hc=d := by
  exact markedPhysicalActivePathIndex_path_injective P hP rfl hd
    (markedPhysicalCoordinateIndexOrder_recovery P hP V pads ψ η d₀ Y Q
      (markedPhysicalActivePathIndex P hP d order) hc hR ha)

end
end ArtinMatthews
