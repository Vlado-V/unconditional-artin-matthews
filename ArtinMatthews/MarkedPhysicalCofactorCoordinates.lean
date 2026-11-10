module

public import ArtinMatthews.MarkedPhysicalEndpointNormPositions
public import ArtinMatthews.MarkedPhysicalEndpointRecovery
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

/-! Exact natural cofactor coordinates for the original physical position
fiber. The literal box and primitive/divisibility conditions are retained
in the coordinate carrier, before any support-specific removal. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun j k => Disjoint (P j) (P k)))
  {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,0≤z.1 ∧ 0≤z.2) (a : MarkedPhysicalMarking P M)

def MarkedPhysicalCofactorCoordinates :=
  {v : ℕ × ℕ // markedPhysicalLift (markedPhysicalMarkingProduct a) v.1 v.2∈Z ∧
    MarkedPhysicalStateCondition (markedPhysicalLift (markedPhysicalMarkingProduct a) v.1 v.2) a}

include hP hdis hZ

theorem markedPhysicalPositionQuotient_lift (z : MarkedPhysicalPositions Z a) :
    markedPhysicalLift (markedPhysicalMarkingProduct a)
      (markedPhysicalPositionQuotient a z).1 (markedPhysicalPositionQuotient a z).2=z.1.1 := by
  have hd := markedPhysicalPosition_product_dvd hP hdis a z
  apply Prod.ext
  · change ((markedPhysicalMarkingProduct a*(z.1.1.1.natAbs/markedPhysicalMarkingProduct a):ℕ):ℤ)=z.1.1.1
    rw [Nat.mul_div_cancel' hd,Int.natCast_natAbs,abs_of_nonneg (hZ _ z.1.2).1]
  · change (z.1.1.2.natAbs:ℤ)=z.1.1.2
    rw [Int.natCast_natAbs,abs_of_nonneg (hZ _ z.1.2).2]

def markedPhysicalPositionCofactorEquiv : MarkedPhysicalPositions Z a ≃
    MarkedPhysicalCofactorCoordinates (Z := Z) a where
  toFun z := ⟨markedPhysicalPositionQuotient a z,by
    rw [markedPhysicalPositionQuotient_lift hP hdis hZ a z]
    exact ⟨z.1.2,z.2⟩⟩
  invFun v := ⟨⟨markedPhysicalLift (markedPhysicalMarkingProduct a) v.1.1 v.1.2,v.2.1⟩,v.2.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact markedPhysicalPositionQuotient_lift hP hdis hZ a z
  right_inv v := by
    apply Subtype.ext
    change ((markedPhysicalMarkingProduct a*v.1.1)/markedPhysicalMarkingProduct a,v.1.2)=v.1
    rw [Nat.mul_div_right _ (markedPhysicalMarkingProduct_pos hP a)]

@[instance_reducible] def markedPhysicalCofactorCoordinates_fintype :
    Fintype (MarkedPhysicalCofactorCoordinates (Z := Z) a) :=
  Fintype.ofEquiv (MarkedPhysicalPositions Z a) (markedPhysicalPositionCofactorEquiv hP hdis hZ a)

theorem markedPhysicalPositions_cofactor_sum (F : MarkedPhysicalPositions Z a → ℂ) :
    letI := markedPhysicalCofactorCoordinates_fintype hP hdis hZ a
    (∑ z : MarkedPhysicalPositions Z a,F z)=
      ∑ v : MarkedPhysicalCofactorCoordinates (Z := Z) a,
        F ((markedPhysicalPositionCofactorEquiv hP hdis hZ a).symm v) := by
  let _ := markedPhysicalCofactorCoordinates_fintype hP hdis hZ a
  exact (Equiv.sum_comp (markedPhysicalPositionCofactorEquiv hP hdis hZ a).symm F).symm

omit hZ in
theorem markedPhysicalCofactorCoordinates_endpoint (α β : ℕ → ℂ)
    (v : MarkedPhysicalCofactorCoordinates (Z := Z) a) :
    markedPhysicalEndpointVector P M α β (markedPhysicalLift (markedPhysicalMarkingProduct a) v.1.1 v.1.2)=
      if MarkedPhysicalBandRough P v.1.1 then conj (α v.1.1)*β v.1.2 else 0 := by
  let s : MarkedPhysicalState P M Z :=
    ⟨(⟨markedPhysicalLift (markedPhysicalMarkingProduct a) v.1.1 v.1.2,v.2.1⟩,a),v.2.2⟩
  have he := markedPhysicalState_support_iff P hP hdis M Z s
  change MarkedPhysicalEndpointSupport P M (markedPhysicalMarkingProduct a*v.1.1) ↔
    MarkedPhysicalBandRough P ((markedPhysicalMarkingProduct a*v.1.1)/markedPhysicalMarkingProduct a) at he
  rw [Nat.mul_div_right _ (markedPhysicalMarkingProduct_pos hP a)] at he
  by_cases hm : MarkedPhysicalBandRough P v.1.1
  · rw [ite_eq_left hm]
    exact markedPhysicalEndpointVector_lift hP hdis a v.2.2.2.1 hm v.1.2 α β
  · have hbad : ¬MarkedPhysicalEndpointSupport P M
        (markedPhysicalLift (markedPhysicalMarkingProduct a) v.1.1 v.1.2).1.natAbs :=
      fun h => hm (he.mp h)
    rw [markedPhysicalEndpointVector,ite_eq_right hbad,ite_eq_right hm]

end
end ArtinMatthews
