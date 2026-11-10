module

public import ArtinMatthews.GiantTwoSidedRootCRTJoin
public import ArtinMatthews.GiantTwoSidedResidueRootSum
public import ArtinMatthews.GiantTwoSidedResidueDensity
public import ArtinMatthews.GiantTwoSidedResidueModelDensity
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

/-! The original fixed-choice physical moment differs from the signed
independent-residue moment by the proved relative root error times its
literal absolute Haar path mass. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedIndependentMoment {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) : ℂ :=
  ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
    if GiantTwoSidedStaticLabels C π τ aux labels ∧
        giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 then
      giantTwoSidedRootScalar C labels π τ aux ζ K *
        (giantTwoSidedIndependentResidueMean labels q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)):ℂ)
    else 0

theorem giantCandidateFixedMoment_root_error (k ell : ℕ) (C₂ A : ℝ) (hA : 0 ≤ A)
    {γ q : ℝ} (hγ : 0<γ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      ∀ (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ) ≤ (Real.log x)^C₂) → ∀ X : ℝ,x^γ ≤ X →
        ∀ (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell),
          ‖giantTwoSidedPhysicalMoment C π τ aux step q ζ K
              (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X) -
            (((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ):ℂ)*giantTwoSidedIndependentMoment C π τ aux step q ζ K‖ ≤ 
          (2*(Real.log x)^(-A*(n:ℝ))+Real.exp (-γ*Real.log x/4))*
            ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*giantTwoSidedIndependentFixedPathMass C π τ aux step q ζ K := by
  filter_upwards [giantCandidatePhysicalMoment_eq_rootMoment k C₂ hγ hq0,
    giantCandidateRootResidue_relative (k+ell) A hA hγ,
    giantCandidateIndependentResidueMean_eq_rootDensity,
    giantCandidateSelectedGroups_geometry_eventually,
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hphysical hrelative hmodel hgeo hlog
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro C π τ aux step hstep X hX ζ K
  let n := giantTwoSidedSourceMomentLength x
  let L := ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)
  let E := 2*(Real.log x)^(-A*(n:ℝ))+Real.exp (-γ*Real.log x/4)
  have hE : 0 ≤ E := add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (zero_le_one.trans hlog) _)) (Real.exp_nonneg _)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  rw [hphysical S ell C π τ aux step hstep X hX ζ K,
    giantTwoSidedRootMoment_static (hgeo S).1]
  unfold giantTwoSidedIndependentMoment
  rw [mul_sum,← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
        (E*L)*(if GiantTwoSidedResidueLabelGuard C π τ aux labels then
          ‖giantTwoSidedRootScalar C labels π τ aux ζ K‖*
            giantTwoSidedIndependentResidueMean labels q
              (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) else 0) := by
      apply sum_le_sum
      intro labels _
      let offset := giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)
      let mean := giantTwoSidedIndependentResidueMean labels q offset
      let scalar := giantTwoSidedRootScalar C labels π τ aux ζ K
      have hmean : 0 ≤ mean := giantTwoSidedIndependentResidueMean_nonneg labels hq0 offset
      have hmass : 0 ≤ (if GiantTwoSidedResidueLabelGuard C π τ aux labels then ‖scalar‖*mean else 0) := by
        split_ifs
        · exact mul_nonneg (norm_nonneg _) hmean
        · exact le_rfl
      by_cases hg : GiantTwoSidedStaticLabels C π τ aux labels ∧ offset (Fin.last n)=0
      · have hguard : GiantTwoSidedResidueLabelGuard C π τ aux labels := hg.1
        rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hguard]
        have hsum : (∑ root : ↥(giantTwoSidedRootInterval X),
            giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels)) =
            scalar*(∑ root∈giantTwoSidedRootInterval X,
              giantTwoSidedRootResidueFactor P labels q offset (root:ℤ):ℝ) := by
          simp only [giantTwoSidedRootWeight,← mul_sum,← Complex.ofReal_sum]
          exact congrArg (fun z : ℝ => scalar*(z:ℂ))
            (sum_coe_sort (giantTwoSidedRootInterval X) (fun root : ℕ =>
              giantTwoSidedRootResidueFactor P labels q offset (root:ℤ)))
        rw [hsum]
        have hr := hrelative S labels q hq0 hq1 offset X hX
        rw [← hmodel S nz (k+ell) labels q offset] at hr
        change |(∑ root∈giantTwoSidedRootInterval X,
          giantTwoSidedRootResidueFactor P labels q offset (root:ℤ))-L*mean| ≤ E*(L*mean) at hr
        have he : scalar*(∑ root∈giantTwoSidedRootInterval X,
            giantTwoSidedRootResidueFactor P labels q offset (root:ℤ):ℝ) -
            (L:ℂ)*(scalar*(mean:ℂ)) =
            scalar*((((∑ root∈giantTwoSidedRootInterval X,
              giantTwoSidedRootResidueFactor P labels q offset (root:ℤ))-L*mean:ℝ):ℂ)) := by
          push_cast
          ring
        rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left hr (norm_nonneg scalar)).trans_eq (by ring)
      · rw [ite_eq_right hg,ite_eq_right hg,mul_zero,sub_self,norm_zero]
        exact mul_nonneg (mul_nonneg hE hL) hmass
    _ = E*L*giantTwoSidedIndependentFixedPathMass C π τ aux step q ζ K := by
      rw [← mul_sum]
      rfl

end
end ArtinMatthews
