module

public import ArtinMatthews.SourceComparisonActualBands
public import ArtinMatthews.SourceComparisonLiteralMarks
public import ArtinMatthews.SourceComparisonMarkedDivisors
public import ArtinMatthews.SourceComparisonActualDivisorBudget
public import ArtinMatthews.SourceComparisonDivisorMass
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

/-! The actual marked weight and its literal retained model satisfy the
damped pointwise, divisor support, reciprocal mass and squared-error bounds. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

universe u v
variable {J : Type u} [Fintype J]

theorem sourceComparisonActualInertActiveModel_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {r : ℝ} (hr : (1/2:ℝ) ≤ r) (hr₁ : r < 1) (A : ℝ) :
    ∃ D E K : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ 0 ≤ K ∧
      ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x)
        (t : G → ℕ), (∀ g, t g ≤ m) →
        ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ r) →
        ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
          (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
        let P := sourceComparisonActualBands e x i
        let u := Sum.elim (fun _ => 1) t
        let q' := Sum.elim (fun _ => 1/2) q
        let b' (l : (g : J ⊕ G) → Fin (u g) → ℕ) := b (fun g => l (.inr g))
        let L := Real.log x
        let j := ⌊L ^ (1/100:ℝ)⌋₊
        let I := sourceComparisonDivisorIndices P u j
        let H := sourceComparisonInertActiveMarks e x (giantCandidateGroup x ∘ i) t q b
        (∀ n, ‖H n‖ ≤ L ^ D) ∧
        (∀ z ∈ I, 0 < sourceComparisonDivisor z ∧
          (sourceComparisonDivisor z : ℝ) ≤ Real.exp (K * L ^ (47/100:ℝ)) ∧
          ∀ p : ℕ, p.Prime → p ∣ sourceComparisonDivisor z → p ∈ univ.biUnion P) ∧
        (∑ z ∈ I, ‖sourceComparisonDivisorCoefficient P u q' b' z‖ /
          (sourceComparisonDivisor z : ℝ)) ≤ L ^ E ∧
        ∀ N : ℕ, (∑ n ∈ Ioc 0 N, ‖H n - sourceComparisonDivisorModel P u q' b' j n‖ ^ 2) ≤
          (N : ℝ) * L ^ (-A) := by
  have hr₀ := (by norm_num : (0:ℝ) < 1/2).trans_le hr
  obtain ⟨D, E, K, hD, hE, hK, hbudget⟩ :=
    sourceComparisonActualDivisorBudget_eventually.{u,v} e he heinj m hr₀ hr₁ A
  refine ⟨D, E, K, hD, hE, hK, ?_⟩
  filter_upwards [sourceComparisonActualBands_geometry_eventually.{u,v} e he heinj, hbudget,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hG hbudget hL
  intro G _ i t ht q hq b hb
  let P := sourceComparisonActualBands e x i
  let u : J ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let q' : J ⊕ G → ℝ := Sum.elim (fun _ => 1/2) q
  let b' (l : (g : J ⊕ G) → Fin (u g) → ℕ) := b (fun g => l (.inr g))
  let L := Real.log x
  let j := ⌊L ^ (1/100:ℝ)⌋₊
  let Z := Real.exp (L ^ (46/100:ℝ))
  let V := ∑ p ∈ univ.biUnion P, 1 / (p : ℝ)
  let I := sourceComparisonDivisorIndices P u j
  let H := sourceComparisonInertActiveMarks e x (giantCandidateGroup x ∘ i) t q b
  have hV₀ : 0 ≤ V := by unfold V; positivity
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hZ : 1 ≤ Z := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hL₀.le _)
  obtain ⟨hdis, hV, hp, _⟩ := hG i
  obtain ⟨hV', _, hDamp, hErr, hRaw⟩ := hbudget i t ht
  have hq' (g : J ⊕ G) : 0 ≤ q' g ∧ q' g ≤ r := by
    rcases g with g | g
    · change 0 ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ r
      exact ⟨by norm_num, hr⟩
    · exact hq g
  have hq₁ (g : J ⊕ G) : 0 ≤ q' g ∧ q' g ≤ 1 :=
    ⟨(hq' g).1, (hq' g).2.trans hr₁.le⟩
  have hb' : ∀ l ∈ sourceComparisonMarkChoices P u, ‖b' l‖ ≤ 1 := by
    intro l hl
    have hc := (mem_sourceComparisonMarkChoices P u l).mp hl
    apply hb
    exact (mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t (fun g => l (.inr g))).mpr
      ⟨fun g z => hc.1 (.inr g) z, fun g => hc.2 (.inr g)⟩
  have hVpos (g : J ⊕ G) : 0 < bandReciprocalMass (P g) :=
    (by positivity : 0 < Real.log 2 / 2).trans (hV g).1
  have hp' : ∀ p ∈ univ.biUnion P, p.Prime := fun p h => (hp p h).1
  have hCoeff := sourceComparisonDivisorCoefficient_reciprocal_bound P u q' j hdis hVpos hq₁ b' hb'
  refine ⟨fun n => (sourceComparisonMarkWeight_damped_bound P u q' b' hb' hVpos hr₀ hr₁ hq' n).trans hDamp,
    ?_, hCoeff.trans ?_, ?_⟩
  · intro z hz
    refine ⟨sourceComparisonDivisor_pos P u j hp' hz, ?_,
      fun p hp hd => sourceComparisonDivisor_prime_dvd_mem P u j hz hp hd hp'⟩
    apply (sourceComparisonDivisor_bound P u j hZ (fun p h => (hp p h).2.2) hz).trans
    exact (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hZ) _)
      (Real.one_le_exp_iff.mpr hV₀)).trans hRaw
  · change Real.exp V ≤ L ^ E
    rw [Real.rpow_def_of_pos hL₀, mul_comm (Real.log L) E]
    exact Real.exp_le_exp.mpr hV'
  · intro N
    apply (sourceComparisonDivisorModel_l2_error P u q' hdis hq₁ hVpos hp' b' hb' j N).trans
    have he := mul_le_mul_of_nonneg_left hErr (Nat.cast_nonneg (α := ℝ) N)
    simpa only [sourceComparisonDivisorErrorBudget, mul_div_assoc, mul_assoc] using he

end
end ArtinMatthews
