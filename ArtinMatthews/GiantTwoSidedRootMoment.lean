module

public import ArtinMatthews.GiantTwoSidedRootAdmissible
public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantTwoSidedPathSupport
public import ArtinMatthews.GiantTwoSidedRootWeightedSum
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original fixed-pattern moment sums all physical paths. Its
exact root-label form keeps the position return condition and allows
independent ordered lists at the two endpoints. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedPhysicalMoment {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) : ℂ :=
  ∑ s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z,
    if (s 0).val.1.val∈I then
      (if (s (Fin.last n)).val.1.val=(s 0).val.1.val then
        (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ) else 0)*
      (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
        (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) else 0

def giantTwoSidedRootMoment {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (I : Finset ℕ) : ℂ :=
  ∑ r : ↥I,∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
    if GiantTwoSidedRootAdmissible C π τ aux step (r,labels) ∧
        giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 then
      giantTwoSidedRootWeight C π τ aux step q ζ K (r,labels) else 0

theorem giantCandidatePhysicalMoment_eq_rootMoment (k : ℕ) (C₂ : ℝ)
    {γ q : ℝ} (hγ : 0<γ) (hq : 0≤q) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell),
          giantTwoSidedPhysicalMoment C π τ aux step q ζ K
            (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X) =
          giantTwoSidedRootMoment C π τ aux step q ζ K (giantTwoSidedRootInterval X) := by
  filter_upwards [giantCandidatePhysicalPath_root_sum (A:=ℂ) k C₂ hγ,
    giantCandidateSelectedGroups_geometry_eventually,
    Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hs hgeo hL
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX ζ K
  unfold giantTwoSidedPhysicalMoment
  rw [giantTwoSidedPhysicalPath_sum_support C π τ aux step q ζ K]
  let f (d : GiantTwoSidedRootLabelData
      (P:=fun i : S => giantCandidateGroup x i.val) k ell (giantTwoSidedSourceMomentLength x)
      (giantTwoSidedRootInterval X)) :=
    if giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.2 π aux step)
        (Fin.last (giantTwoSidedSourceMomentLength x))=0 then
      giantTwoSidedRootWeight C π τ aux step q ζ K d else 0
  calc
    _ = ∑ s : GiantTwoSidedPhysicalPath C π τ aux step
          (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X),
        f (giantTwoSidedRootLabel_encode s).val := by
      apply sum_congr rfl
      intro s _
      dsimp only [f]
      simp only [giantTwoSidedPhysicalPath_root_loop s]
      split_ifs
      · exact giantTwoSidedPhysicalPath_root_weight (hgeo S).1
          (giantTwoSidedSourceMomentLength_pos hL).ne' s hq ζ K
      · exact zero_mul _
    _ = _ := by
      rw [hs S ell C π τ aux step hstep X hX f]
      unfold giantTwoSidedRootMoment
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro labels _
      dsimp only [f]
      by_cases ha : GiantTwoSidedRootAdmissible C π τ aux step (r,labels) <;>
        by_cases hl : giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)
          (Fin.last (giantTwoSidedSourceMomentLength x))=0 <;> simp [ha,hl]

end
end ArtinMatthews
