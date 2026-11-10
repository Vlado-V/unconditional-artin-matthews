module

public import ArtinMatthews.GiantArrayRemoval
public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantPrimeExtractionArithmetic
public import ArtinMatthews.GiantExtractionCutoff
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

/-! Exact finite extraction with the actual unit-residue restriction.
The full character expansion and the original predecessor support are
preserved before taking any limits. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Classical
noncomputable section

def giantFixedProgressionExtractionPrime {M : ℕ} (U : Finset (ZMod M)ˣ)
    {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ)
    (T x : ℝ) : ℂ :=
  ∑ n∈(Ioc 0 ⌊T*x⌋₊).filter Nat.Prime,
    markedExtractionWeight e G Φ x n*giantUnitResidueIndicator U (n:ZMod M)

def giantFixedProgressionExtractionRough {M : ℕ} (U : Finset (ZMod M)ˣ)
    {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ)
    (T γ x : ℝ) : ℂ :=
  ∑ n∈roughPositiveUpTo ⌊T*x⌋₊ (x^γ),
    markedExtractionWeight e G Φ x n*giantUnitResidueIndicator U (n:ZMod M)

theorem giantFixedProgressionExtractionPrime_eq_character_sum {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T x : ℝ) :
    giantFixedProgressionExtractionPrime U e G Φ T x =
      ∑ χ : DirichletCharacter ℂ M,giantResidueCharacterCoefficient U χ*giantOrdinaryPrimeSum e χ G Φ T x :=
  giantUnitResidueIndicator_weighted_sum U _ (markedExtractionWeight e G Φ x)

theorem giantFixedProgressionExtractionRough_eq_character_sum {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) :
    giantFixedProgressionExtractionRough U e G Φ T γ x =
      ∑ χ : DirichletCharacter ℂ M,giantResidueCharacterCoefficient U χ*giantOrdinaryRoughSum e χ G Φ T γ x :=
  giantUnitResidueIndicator_weighted_sum U _ (markedExtractionWeight e G Φ x)

theorem giantFixedProgressionExtractionPrime_eq_predecessor {M : ℕ}
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) {T x : ℝ} (hT : 0≤T) (hx : 1≤x) (hhigh : ∀ t,T<t → Φ t=0) :
    giantFixedProgressionExtractionPrime U e G Φ (T+1) x =
      ∑ u∈(Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime),
        (Φ ((u:ℝ)/x):ℂ)*giantUnitResidueIndicator U ((u+1:ℕ):ZMod M)*G x u*
          (literalMarkedArrayWeight e x u:ℂ) := by
  unfold giantFixedProgressionExtractionPrime
  rw [giantExtraction_predecessor_reindex T x hT hx Nat.Prime _
    (fun n hn => by rw [markedExtractionWeight_eq_zero_of_past e G Φ (zero_lt_one.trans_le hx) hhigh hn,zero_mul])]
  apply sum_congr rfl
  intro u _
  simp only [markedExtractionWeight,Nat.add_sub_cancel]
  ring

theorem giantFixedProgressionExtractionRough_eq_predecessor {M : ℕ}
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (γ : ℝ) {T x : ℝ} (hT : 0≤T) (hx : 1≤x) (hhigh : ∀ t,T<t → Φ t=0) :
    giantFixedProgressionExtractionRough U e G Φ (T+1) γ x =
      ∑ u∈(Icc 0 ⌊T*x⌋₊).filter (fun u => MarkedRoughAbove (x^γ) (u+1)),
        (Φ ((u:ℝ)/x):ℂ)*giantUnitResidueIndicator U ((u+1:ℕ):ZMod M)*G x u*
          (literalMarkedArrayWeight e x u:ℂ) := by
  classical
  unfold giantFixedProgressionExtractionRough roughPositiveUpTo
  rw [giantExtraction_predecessor_reindex T x hT hx (MarkedRoughAbove (x^γ)) _
    (fun n hn => by rw [markedExtractionWeight_eq_zero_of_past e G Φ (zero_lt_one.trans_le hx) hhigh hn,zero_mul])]
  apply sum_congr rfl
  intro u _
  simp only [markedExtractionWeight,Nat.add_sub_cancel]
  ring

theorem giantFixedProgressionExtraction_weight_eq_literal_eventually {M : ℕ}
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ)
    (ε : ℝ) (hε : ε≤1/4) (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦzero : Φ 0=0) :
    ∀ᶠ x : ℝ in atTop,∀ u∈Icc 0 ⌊T*x⌋₊,
      (Φ ((u:ℝ)/x):ℂ)*giantUnitResidueIndicator U ((u+1:ℕ):ZMod M)*giantMarkedCenteredCore ε x u*
          (literalMarkedArrayWeight e x u:ℂ) =
        (Φ ((u:ℝ)/x):ℂ)*giantFixedResidueLiteralCoefficient U ε x u*
          (literalMarkedArrayWeight e x u:ℂ) := by
  filter_upwards [giant_fixed_residue_test_eq U ε T hε hT Φ hΦzero] with x hx
  intro u hu
  have h := congrArg (fun z : ℂ => z*(literalMarkedArrayWeight e x u:ℂ)) (hx u hu).symm
  simpa only [giantFixedResidueCenteredCoefficient,giantMarkedCenteredCore,mul_assoc] using h

theorem giantFixedProgressionExtractionPrime_div_eq_array_eventually {M : ℕ}
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    (ε : ℝ) (hε : ε≤1/4) (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦzero : Φ 0=0)
    (hhigh : ∀ t,T<t → Φ t=0) :
    ∀ᶠ x : ℝ in atTop,
      giantFixedProgressionExtractionPrime U e (giantMarkedCenteredCore ε) Φ (T+1) x /
        (literalMarkedArrayMean e x:ℂ) = giantFixedProgressionArrayPrimeSum U e ε Φ T x := by
  filter_upwards [giantFixedProgressionExtraction_weight_eq_literal_eventually U e ε hε Φ hT hΦzero,
    eventually_ge_atTop (1:ℝ)] with x hl hx
  rw [giantFixedProgressionExtractionPrime_eq_predecessor U e _ Φ hT hx hhigh]
  unfold giantFixedProgressionArrayPrimeSum markedPrimeSingleArrayCorrelation
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro u hu
  rw [hl u (mem_filter.mp hu).1,Complex.ofReal_div]
  change _ = (Φ ((u:ℝ)/x):ℂ)*giantFixedResidueLiteralCoefficient U ε x u*
    ((literalMarkedArrayWeight e x u:ℂ)/(literalMarkedArrayMean e x:ℂ))
  ring

end
end ArtinMatthews
