module

public import ArtinMatthews.GiantCandidateModelMomentRealization
public import ArtinMatthews.GiantCandidateActualBoundedTests
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

/-! Each actual chosen group contributes the two literal hit counts.
Distinct chosen groups satisfy the uniform comparison hypotheses. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

def giantCandidateHitSideOfBool (b : Bool) : GiantCandidateHitSide :=
  if b then .predecessor else .product

theorem giantCandidateHitSideOfBool_injective : Function.Injective giantCandidateHitSideOfBool := by
  intro b c h
  cases b <;> cases c <;> simp [giantCandidateHitSideOfBool] at h ⊢

theorem giant_candidate_actual_group_tests_uniform (r : ℕ) (τ : ℝ) (hτ : 0<τ)
    {j : ℕ} (hj : 0<j) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ g : Fin r → GiantCandidateGroupIndex x,Function.Injective g →
      let G (i : Fin r × Bool) := giantCandidateGroup x (g i.1)
      let side (i : Fin r × Bool) := giantCandidateHitSideOfBool i.2
      ∃ hG : ∀ i p,p∈G i → p.Prime,
        ∀ H : Fin j → ℕ,(∀ v,x^τ≤(H v:ℝ)) →
        ∀ f : (Fin r × Bool → ℕ) → ℝ,(∀ k,|f k|≤1) →
        let W := Real.exp ((Real.log x)^(6/25:ℝ))
        let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
        |(𝔼 t∈Fintype.piFinset S,f (giantCandidateActualHitCounts G side t))-
          (𝔼 t∈giantCandidateModelResidueTuples G hG j,f (giantCandidateModelHitCounts G side t))|≤δ := by
  let side (i : Fin r × Bool) := giantCandidateHitSideOfBool i.2
  filter_upwards [giant_candidate_actual_bounded_count_tests_uniform side τ hτ hj zero_le_one hδ,
    giantCandidateGroup_mass_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hcompare hmass hx hL
  intro g hg G side'
  have hsub (i : Fin r × Bool) : G i⊆giantCandidateFullPrimes x :=
    fun p hp => mem_giantCandidateFullPrimes.mpr ⟨g i.1,hp⟩
  have hdis : Pairwise (fun i l => side' i=side' l → Disjoint (G i) (G l)) := by
    intro i l hil hside
    have hb : i.2=l.2 := giantCandidateHitSideOfBool_injective hside
    have ha : i.1≠l.1 := fun h => hil (Prod.ext h hb)
    exact giantCandidateGroup_pairwise_disjoint hx hL (hg.ne ha)
  have hmass' (i : Fin r × Bool) : (∑ p∈G i,1/(p:ℝ))≤1 := (hmass (g i.1)).2.le
  exact hcompare G hsub hdis hmass'

end
end ArtinMatthews
