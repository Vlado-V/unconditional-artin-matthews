module

public import ArtinMatthews.GiantTwoSidedLabelOffsets
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

/-! The actual subpower displacement preserves the positive interval
slice used for the physical moment. Every root in the original dyad
has all its visits inside the same explicit enlarged finite slice. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

def giantTwoSidedRootInterval (X : ℝ) : Finset ℕ := Ico ⌈X⌉₊ ⌈2*X⌉₊

def giantTwoSidedRootSlice (X : ℝ) : Finset ℕ := Ioc 0 ⌈3*X⌉₊

theorem giantTwoSidedSourceMomentLength_pos {x : ℝ} (hL : 0<Real.log x) :
    0<giantTwoSidedSourceMomentLength x :=
  Nat.mul_pos (by decide) (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL _))

theorem giantTwoSidedRootInterval_bounds {X : ℝ} {r : ℕ}
    (hr : r∈giantTwoSidedRootInterval X) : X≤(r:ℝ) ∧ (r:ℝ)<2*X :=
  ⟨(Nat.le_ceil X).trans (Nat.cast_le.mpr (mem_Ico.mp hr).1),Nat.lt_ceil.mp (mem_Ico.mp hr).2⟩

theorem giantTwoSidedRootInterval_translate {X : ℝ} (hX : 0<X) {r : ℕ}
    (hr : r∈giantTwoSidedRootInterval X) {h : ℤ} (hh : |(h:ℝ)|≤X/2) :
    0<(r:ℤ)+h ∧ ((r:ℤ)+h).toNat∈giantTwoSidedRootSlice X := by
  obtain ⟨hrlo,hrhi⟩ := giantTwoSidedRootInterval_bounds hr
  obtain ⟨hhlo,hhhi⟩ := abs_le.mp hh
  have hlo : 0<(r:ℝ)+(h:ℝ) := by linarith
  have hhi : (r:ℝ)+(h:ℝ)<3*X := by linarith
  have hz : 0<(r:ℤ)+h := by exact_mod_cast hlo
  have hnat : (((r:ℤ)+h).toNat:ℝ)=(r:ℝ)+(h:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz.le
  refine ⟨hz,mem_Ioc.mpr ⟨?_,?_⟩⟩
  · have hnatpos : (0:ℝ)<(((r:ℤ)+h).toNat:ℝ) := by rw [hnat]; exact hlo
    exact_mod_cast hnatpos
  · apply (Nat.cast_le (α:=ℝ)).mp
    rw [hnat]
    exact hhi.le.trans (Nat.le_ceil (3*X))

theorem giantCandidateLabelRoot_margin (k : ℕ) (C₂ : ℝ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
        (π : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ r∈giantTwoSidedRootInterval X,∀ v : Fin (n+1),
          0<(r:ℤ)+giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) v ∧
          ((r:ℤ)+giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) v).toNat∈
            giantTwoSidedRootSlice X := by
  have hγ2 : 0<γ/2 := half_pos hγ
  filter_upwards [giantCandidateLabelOffsets_subpower k C₂ hγ2,eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop hγ2).eventually_ge_atTop (2:ℝ)] with x hoff hx hlarge
  intro S
  dsimp only
  intro ell C labels π aux step hstep X hX r hr v
  have hX0 : 0<X := (Real.rpow_pos_of_pos hx γ).trans_le hX
  have hpow : x^γ=(x^(γ/2))^2 := by
    rw [sq,← Real.rpow_add hx]
    congr 1
    ring
  have hbound : x^(γ/2)≤X/2 := by
    rw [hpow] at hX
    have hmul := mul_le_mul_of_nonneg_right hlarge (zero_le_two.trans hlarge)
    nlinarith only [hX,hmul]
  exact giantTwoSidedRootInterval_translate hX0 hr
    ((hoff S ell C labels π aux step hstep v).trans hbound)

end
end ArtinMatthews
