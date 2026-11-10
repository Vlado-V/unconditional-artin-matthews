module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.GiantSignedSourceVisitWeights
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.MarkedPhysicalPrimeHitProduct
public import ArtinMatthews.GiantSignedSourceInitialConditionalMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The exact return character and the actual big-prime baseline at
the source visit schedule. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section

theorem giantSignedReturnPhase_eq_fourier (θ : ℝ) (κ : ℤ) (D : ℕ) :
    idealAdditivePhase (θ*(κ : ℝ)) D =
      fourier (κ*(D : ℤ)) (θ : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, idealAdditivePhase]
  push_cast
  rw [div_one]
  congr 1
  ring

theorem giantSignedSourceBigBaseline_eventually
    {q c C₀ vmin : ℝ} (k ell : ℕ) (hM : 1 ≤ k+ell)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hvmin : 0 < vmin) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (B : Type*) [Fintype B] (PB : B → Finset ℕ),
        (∀ g, vmin ≤ bandReciprocalMass (PB g)) →
        (∀ g (p : PB g), Real.exp ((Real.log x)^c) ≤ (p.val : ℝ)) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
        let visitQ := giantSignedSourceVisitQ q (giantTwoSidedSourceMomentLength x)
        let base := fun p : ↥(markedPhysicalBandPrimes PB) => giantSignedPrimeBaseline visitQ p.val
        (∀ p, 0 < base p) ∧ 0 ≤ (∏ p, base p) ∧ (∏ p, base p) ≤ 1 := by
  filter_upwards [giantSignedSourceInitialConditionalMass_eventually k ell hM hq0 hq1 hc hC₀ hvmin]
    with x hx
  intro B _ PB hV hp hgroups
  let n := giantTwoSidedSourceMomentLength x
  let L := Real.log x
  let visitQ := giantSignedSourceVisitQ q n
  let Pmin := Real.exp (L^c)
  have hmass := (hx B PB hV hp hgroups).1
  have hden : 0 < 1-((n+1 : ℕ) : ℝ)/Pmin :=
    inv_pos.mp (zero_lt_one.trans_le hmass)
  have hn : ((n+1 : ℕ) : ℝ) < Pmin := (div_lt_one (Real.exp_pos _)).mp (by linarith)
  have hn' (p : ↥(markedPhysicalBandPrimes PB)) : n+1 < p.val := by
    obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp p.property
    exact_mod_cast hn.trans_le (hp g ⟨p.val,hg⟩)
  have hq0i (i : Fin (n+1)) : 0 ≤ visitQ i := (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
  have hq1i (i : Fin (n+1)) : visitQ i ≤ 1 := by
    have hs : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
    exact (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2.trans hs
  have hb0 (p : ↥(markedPhysicalBandPrimes PB)) : 0 < giantSignedPrimeBaseline visitQ p.val :=
    giantSignedPrimeBaseline_pos_of_length visitQ hq0i (hn' p)
  have hb1 (p : ↥(markedPhysicalBandPrimes PB)) : giantSignedPrimeBaseline visitQ p.val ≤ 1 :=
    sub_le_self _ (div_nonneg (giantSignedVisitLoss_nonneg visitQ hq1i) (Nat.cast_nonneg _))
  exact ⟨hb0, Finset.prod_nonneg (fun p _ => (hb0 p).le),
    Finset.prod_le_one₀ (fun p _ => (hb0 p).le) (fun p _ => hb1 p)⟩

end
end ArtinMatthews
