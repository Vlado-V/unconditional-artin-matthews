module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantComparisonCutoffPairing
public import ArtinMatthews.GiantComparisonSeparatedSum
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantComparisonAuxiliaryRestoration
public import ArtinMatthews.GiantComparisonRestorationEnvelope
public import ArtinMatthews.GiantComparisonStripSupport
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

/-! The physical cutoff for a performed comparison differs from its
independent-list expression by an arbitrary inverse log power times
the actual coefficient norm bound. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateComparisonCutoff_independent_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i ≤ 1/5) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m)
    {γ : ℝ} (hγ : 0 < γ) (j : ℕ) (hj : 0 < j) (k : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (Ψ : ℝ → ℂ)
    {a b B : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ y ∉ Set.Icc a b, Ψ y = 0) (hB : ∀ y, ‖Ψ y‖ ≤ B) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x))
        (CB : GiantCandidatePerformedBig S → Finset (Fin k)),
      let P (g : S) := giantCandidateGroup x g.val
      let C₀ := giantCandidatePerformedPattern S CB
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      ∀ (K : GiantTwoSidedPatternCoefficient P C₀ 1) (L : GiantComparisonListCoefficient P C₀ 1)
        (M : ℝ), 0 ≤ M →
      (∀ c b b' aux, K (giantComparisonJoinLabels c b) (giantComparisonJoinLabels c b') aux = L b b' aux) →
      (∀ b b' aux, ‖L b b' aux‖ ≤ M) →
      ‖giantTwoSidedPhysicalPatternCutoffPairing (Z:=Ioc 0 ⌊x^2⌋₊) C₀ 1 q 0
          (giantComparisonCharacterCoefficient χ K) Ψ x
          (fun n => (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)*conj (F n))
          (fun t => (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ)*
            χ t.val.1.val*G t.val.1.val) -
        (∑ aux : GiantTwoSidedPatternAuxiliary P C₀,
          giantComparisonIndependentAuxiliarySum ⌊x^2⌋₊ x q Ψ χ F G L aux)‖ ≤
        C*M*(Real.log x)^(-A) := by
  have he' (i : I) : 0 < e i ∧ e i < 1 := ⟨(he i).1,(he i).2.trans_lt (by norm_num)⟩
  obtain ⟨C,hC,hrows⟩ := giantCandidateComparisonRestorationEnvelope_eventually
    e he' hε hεq hm χ hγ j hj k hq hq1 Ψ ha hb hΨ hB A
  have hsupp : Function.support Ψ ⊆ Set.Iic (b+1) := by
    intro y hy
    have hmem : y ∈ Set.Icc a b := by
      by_contra hn
      exact hy (hΨ y hn)
    exact hmem.2.trans (by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [hrows,giantCandidateComparisonCutoff_eq_unmasked_eventually
    e (fun i => (he i).2) hεq hm χ γ j k q (by linarith : 0 < b+1) hsupp,
    giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually]
    with x hrow hcut hgeo hprime
  intro S CB
  dsimp only
  intro K L M hM hK hL
  let P (g : S) := giantCandidateGroup x g.val
  let C₀ := giantCandidatePerformedPattern S CB
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  let N := ⌊x^2⌋₊
  let W := giantComparisonOrderedFreeWeight P C₀ 1 q
  let Z := GiantTwoSidedPatternAuxiliary P C₀
  have hP (g : S) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp⟩)).1
  have hV (g : S) : 0 < bandReciprocalMass (P g) :=
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 g).1
  rw [hcut S C₀ K,← sum_sub_distrib]
  calc
    _ ≤ ∑ aux : Z, ‖(∑ u : GiantComparisonUnmaskedEdge P C₀ 1 N aux,
        giantComparisonUnmaskedSummand x q Ψ χ F G K u) -
        giantComparisonIndependentAuxiliarySum N x q Ψ χ F G L aux‖ := norm_sum_le _ _
    _ ≤ ∑ aux : Z, giantTwoSidedPatternAuxiliaryMass aux*(M*(C*(Real.log x)^(-A))) := by
      apply sum_le_sum
      intro aux _
      have hE := giantComparisonUnmaskedAuxiliary_error (N:=N) hP (hgeo S).1 hV x hq hq1 Ψ χ F G K L aux
        (fun c b b' => hK c b b' aux) hM (fun b b' => hL b b' aux)
      refine hE.trans ?_
      apply mul_le_mul_of_nonneg_left _ (giantTwoSidedPatternAuxiliaryMass_nonneg hV aux)
      let d := giantTwoSidedPatternAuxiliaryProduct aux
      let V (w : ℕ) := ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d)
      let R (w : ℕ) := giantComparisonRestorationLoss aux q w (w+d)
      change (∑ w : ↥(Ioc 0 N), V w.val*M*R w.val) ≤ M*(C*(Real.log x)^(-A))
      rw [Finset.sum_coe_sort (Ioc 0 N) (fun w : ℕ => V w*M*R w)]
      have hmul : (∑ w ∈ Ioc 0 N, V w*M*R w) = M*(∑ w ∈ Ioc 0 N, V w*R w) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro w _
        ring
      change (∑ w ∈ Ioc 0 N, V w*M*R w) ≤ M*(C*(Real.log x)^(-A))
      rw [hmul]
      exact mul_le_mul_of_nonneg_left (hrow S CB aux) hM
    _ = _ := by
      rw [← sum_mul,giantTwoSidedPatternAuxiliaryMass_sum C₀ hV,one_mul]
      ring

end
end ArtinMatthews
