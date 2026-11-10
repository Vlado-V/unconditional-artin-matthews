module

public import ArtinMatthews.MarkedPhysicalScalarDetector
public import ArtinMatthews.MarkedTypeIIDyadQuotient
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
public import Mathlib.Tactic.Basify
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact pointwise comparison of the occupied Cauchy determinant with
the original scalar delta detector. Quotient labels and physical labels
are swapped, so the determinant is literally bmn−ars. -/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate Classical
noncomputable section

theorem markedTypeIIDeterminantSum_filter_of_zero (E : Finset MarkedTypeIIEndpoint)
    (p : MarkedTypeIIEndpoint → Prop) [DecidablePred p] (c : MarkedTypeIIEndpoint → ℂ)
    (hc : ∀ a∈E,¬p a → c a=0) :
    markedTypeIIDeterminantSum (E.filter p) c=markedTypeIIDeterminantSum E c := by
  unfold markedTypeIIDeterminantSum
  calc
    _ = ∑ a∈E.filter p,∑ b∈E,if a.label.Coprime b.label ∧
        markedTypeIIDeterminant a b=(b.label:ℤ)-a.label then c a*conj (c b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b hb hnot
      have hz := hc b hb (fun hp => hnot (Finset.mem_filter.mpr ⟨hb,hp⟩))
      simp [hz]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a ha hnot
      have hz := hc a ha (fun hp => hnot (Finset.mem_filter.mpr ⟨ha,hp⟩))
      simp [hz]

theorem markedTypeII_occupied_determinant_eq_full {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (M N : Finset ℕ) (α β : ℕ → ℂ) :
    markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y M N)
      (markedTypeIILabelEndpointCoefficient P Y α β) =
    markedTypeIIDeterminantSum (giantMarkedEndpoints P M N)
      (markedTypeIILabelEndpointCoefficient P Y α β) := by
  apply markedTypeIIDeterminantSum_filter_of_zero
  intro a _ h
  have hz : markedTypeIILabelCutoff ((a.label:ℝ)/Y)=0 := not_not.mp h
  simp [markedTypeIILabelEndpointCoefficient,hz]

theorem markedTypeII_dyad_delta_term {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (ψ : ℝ → ℂ) (α β : ℕ → ℂ)
    (hψ : ∀ t∈Set.Icc (-4:ℝ) 4,ψ t=1) (a b m n r s : ℕ) :
    (if markedTypeIIDeterminant (giantMarkedEndpoint a m n) (giantMarkedEndpoint b r s)=(b:ℤ)-a then
      markedTypeIILabelEndpointCoefficient P Y α β (giantMarkedEndpoint a m n)*
        conj (markedTypeIILabelEndpointCoefficient P Y α β (giantMarkedEndpoint b r s)) else 0)=
    (markedMajorLabelMass P:ℂ)^2*
      markedPhysicalScalarDetectorTerm markedTypeIILabelCutoff Y (markedRawEdgeDeltaDetector ψ Y)
        α β b a (m,n) (r,s) := by
  let t : ℤ := (b:ℤ)*m*n-(a:ℤ)*r*s
  have ht : markedTypeIIDeterminant (giantMarkedEndpoint a m n) (giantMarkedEndpoint b r s)=t := by
    change (b:ℤ)*((m*n:ℕ):ℤ)-(a:ℤ)*((r*s:ℕ):ℤ)=t
    dsimp only [t]
    push_cast
    ring
  rw [ht]
  unfold markedTypeIILabelEndpointCoefficient markedPhysicalScalarDetectorTerm markedPhysicalScalarCofactorTerm
    markedRawEdgeDeltaDetector
  change (if t=(b:ℤ)-a then
      ((markedMajorLabelMass P:ℂ)*markedTypeIILabelCutoff ((a:ℝ)/Y)*α m*β n)*
        conj ((markedMajorLabelMass P:ℂ)*markedTypeIILabelCutoff ((b:ℝ)/Y)*α r*β s) else 0) =
    (markedMajorLabelMass P:ℂ)^2*(markedTypeIILabelCutoff ((b:ℝ)/Y)*
      markedTypeIILabelCutoff ((a:ℝ)/Y)*(ψ ((t:ℝ)/Y)*(if t=(b:ℤ)-a then 1 else 0))*
        (α m*conj (α r)*β n*conj (β s)))
  by_cases hdet : t=(b:ℤ)-a
  · rw [ite_eq_left hdet,ite_eq_left hdet,mul_one]
    by_cases ha : markedTypeIILabelCutoff ((a:ℝ)/Y)=0
    · simp [ha]
    by_cases hb : markedTypeIILabelCutoff ((b:ℝ)/Y)=0
    · simp [hb]
    have hsa := markedTypeIILabelCutoff_support ha
    have hsb := markedTypeIILabelCutoff_support hb
    have harg : ((t:ℝ)/Y)∈Set.Icc (-4:ℝ) 4 := by
      rw [hdet,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,sub_div]
      exact ⟨by linarith [hsa.2,hsb.1],by linarith [hsb.2,hsa.1]⟩
    have hreal (u : ℝ) : conj (markedTypeIILabelCutoff u)=markedTypeIILabelCutoff u :=
      markedTypeIILabelCutoff_star u
    rw [hψ _ harg]
    simp only [map_mul,Complex.conj_ofReal,hreal]
    ring
  · simp only [ite_eq_right hdet,mul_zero,zero_mul]

end
end ArtinMatthews
