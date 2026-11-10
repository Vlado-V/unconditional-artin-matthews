module

public import ArtinMatthews.GiantTwoSidedRootAdmissible
public import ArtinMatthews.GiantTwoSidedRootWeight
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

/-! The actual positive-slice physical path sum has a fixed-label
root parametrization with its original complex coefficient. The
terminal position test leaves the two endpoint label lists free. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalPath_root_loop {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    {I Z : Finset ℕ} (s : GiantTwoSidedPhysicalPath C π τ aux step I Z) :
    (s.val (Fin.last n)).val.1.val=(s.val 0).val.1.val ↔
      giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C
        (giantTwoSidedRootLabel_encode s).val.2 π aux step) (Fin.last n)=0 :=
  giantTwoSidedPatternPath_return_iff s.val π τ aux step s.property.edges

theorem giantCandidatePhysicalPath_weighted_root_sum (k : ℕ) (C₂ : ℝ)
    {γ q : ℝ} (hγ : 0<γ) (hq : 0≤q) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell),
          (∑ s : GiantTwoSidedPhysicalPath C π τ aux step
              (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X),
            (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ)*
              (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
                (giantTwoSidedEndpointPermute (π i) (s.val i.castSucc))
                (giantTwoSidedEndpointPermute (τ i) (s.val i.succ)) (aux i))) =
          ∑ r : ↥(giantTwoSidedRootInterval X),
            ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
              if GiantTwoSidedRootAdmissible C π τ aux step (r,labels) then
                giantTwoSidedRootWeight C π τ aux step q ζ K (r,labels) else 0 := by
  filter_upwards [giantCandidatePhysicalPath_root_sum (A:=ℂ) k C₂ hγ,
    giantCandidateSelectedGroups_geometry_eventually,
    Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hs hgeo hL
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX ζ K
  calc
    _ = ∑ s : GiantTwoSidedPhysicalPath C π τ aux step
          (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X),
        giantTwoSidedRootWeight C π τ aux step q ζ K (giantTwoSidedRootLabel_encode s).val := by
      apply sum_congr rfl
      intro s _
      exact giantTwoSidedPhysicalPath_root_weight (hgeo S).1
        (giantTwoSidedSourceMomentLength_pos hL).ne' s hq ζ K
    _ = _ := hs S ell C π τ aux step hstep X hX
      (giantTwoSidedRootWeight C π τ aux step q ζ K)

end
end ArtinMatthews
