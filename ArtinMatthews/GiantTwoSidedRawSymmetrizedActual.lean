module

public import ArtinMatthews.GiantTwoSidedRawSymmetrization
public import ArtinMatthews.GiantTwoSidedRawCorrelation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal independent permutation average for the actual raw
physical graph has the same quantitative shifted-correlation error. -/
namespace ArtinMatthews
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def giantCandidateActualSymmetrizedRawSum {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {m : ℕ} (χ : DirichletCharacter ℂ m)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j k : ℕ) (x : ℝ) : ℂ :=
  let N := ⌊T*x⌋₊
  let Z := giantTwoSidedRawPositionBox P k N
  let Z' := giantTwoSidedRawPositionBox P k (N+1)
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore C (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  giantTwoSidedRawPermutationAverage
    (giantTwoSidedRawPhysicalTerm (P:=P) (k:=k) (Z:=Z) (Z':=Z') x q (fun t => ((t*Φ t:ℝ):ℂ)) χ F G)

theorem giantCandidateActualSymmetrizedRawSum_eq {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {m : ℕ} (χ : DirichletCharacter ℂ m)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j k : ℕ) (x : ℝ) :
    giantCandidateActualSymmetrizedRawSum C P e χ ε Φ T γ q j k x =
      giantCandidateActualRawPhysicalSum C P e χ ε Φ T γ q j k x :=
  giantTwoSidedRawPermutationAverage_eq _

theorem giantCandidateActualSymmetrizedRawSum_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i ≤ 1/5) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq : 0 < q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) (k : ℕ) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let C := giantCandidateFullPrimes x
      ‖giantCandidateActualSymmetrizedRawSum C P e χ ε Φ T γ q j k x -
        giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x‖ ≤
          (Real.log x)^(-A) := by
  simpa only [giantCandidateActualSymmetrizedRawSum_eq] using
    giantCandidateActualRawPhysicalSum_log_saving e he hε hεq hm χ Φ hΦ hT hhigh hγ hq hq1 j hj k A

end
end ArtinMatthews
