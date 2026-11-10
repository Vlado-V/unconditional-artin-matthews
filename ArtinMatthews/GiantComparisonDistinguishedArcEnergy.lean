module

public import ArtinMatthews.GiantComparisonArcMellin
public import ArtinMatthews.GiantComparisonCutoffRows
public import ArtinMatthews.GiantComparisonEndpointGlobalMoment
public import ArtinMatthews.GiantComparisonMellinTail
public import ArtinMatthews.SourceComparisonSmallMarkReindex
public import ArtinMatthews.GiantComparisonActualArcEnergy
public import ArtinMatthews.SourceComparisonActualHighTime
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The full comparison arc energy on the literal endpoint with a
distinguished one-mark small group. -/
namespace ArtinMatthews

open Filter MeasureTheory Set
open scoped ContDiff
noncomputable section

universe u v
variable {I : Type u} [Fintype I]

theorem giantComparisonDistinguishedArcEnergy_eventually
    (e : I → ℝ) (he : ∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5)
    (hinj : Function.Injective e) (m : ℕ) {ρ : ℝ} (hρ : (1/2 : ℝ) ≤ ρ) (hρ₁ : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {lo hi B : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (hB : hi < B)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Icc lo hi)
    (C D A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (s : GiantCandidateSmallGroupIndex x)
      (i : G ↪ GiantCandidateGroupIndex x)
      (hout : (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i)
      (t : G → ℕ), (∀ g, t g ≤ m) →
      ∀ (q₀ : ℝ), 0 ≤ q₀ → q₀ ≤ ρ →
      ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ ρ) →
      ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
        (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
      ∀ (Y H σ : ℝ), x ≤ Y → Y ≤ x ^ (1 + ε/4) →
        Real.exp ((Real.log x)^(38/100 : ℝ)) ≤ H → H ≤ Real.exp (Real.log x/2) →
        |σ| ≤ (Real.log x)^D →
      ∀ (r : ℚ), (r.den : ℝ) ≤ (Real.log x)^C →
      let J := sourceComparisonDistinguishedGroupEmbedding s i hout
      let T := Real.log x*(Y/H)
      (∫ τ in Icc (-T) T, ‖(Y : ℂ)⁻¹ *
        giantComparisonMellinPolynomial (giantComparisonCutoffRows Y lo hi)
          (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ
            (giantCandidateGroup x ∘ J) (Sum.elim (fun _ => 1) t) (Sum.elim (fun _ => q₀) q)
            (fun l => b (fun g => l (.inr g))))) τ‖ ^ 2) ≤ (Real.log x)^(-A) := by
  have hB₀ : 0 ≤ B := hlo.le.trans (hlohi.trans hB.le)
  have hsB : Function.support ψ ⊆ Icc lo B := hs.trans (Icc_subset_Icc le_rfl hB.le)
  obtain ⟨S,_,hhigh⟩ := sourceComparisonCenteredMellinSum_high_energy.{u,v} e he hinj m
    hρ hρ₁ ψ hlo hB₀ hsB hψ hε hεq D C (A+1) hC (by linarith)
  filter_upwards [hhigh, giantComparisonActualArcEnergy_eventually_of_high.{u,v} e he hinj (m+1)
    hε hεq hlo hlohi hB ψ hψ hs C D S A] with x hhigh hjoin
  intro G _ s i hout t ht q₀ hq₀ hq₀ρ q hq b hb Y H σ hYlo hYhi hHlo hHhi hσ r hr
  let _ : NeZero r.den := ⟨r.den_ne_zero⟩
  let J := sourceComparisonDistinguishedGroupEmbedding s i hout
  let u' : Unit ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let q' : Unit ⊕ G → ℝ := Sum.elim (fun _ => q₀) q
  let b' (l : (g : Unit ⊕ G) → Fin (u' g) → ℕ) := b (fun g => l (.inr g))
  let T := Real.log x*(Y/H)
  have hu (g : Unit ⊕ G) : u' g ≤ m+1 := by
    rcases g with g | g
    · exact Nat.le_add_left 1 m
    · exact (ht g).trans (Nat.le_succ m)
  have hq' (g : Unit ⊕ G) : 0 ≤ q' g ∧ q' g ≤ 1 := by
    rcases g with g | g
    · exact ⟨hq₀,hq₀ρ.trans hρ₁.le⟩
    · exact ⟨(hq g).1,(hq g).2.trans hρ₁.le⟩
  have hb' : ∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ J) u', ‖b' l‖ ≤ 1 := by
    intro l hl
    have h := (mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ J) u' l).mp hl
    exact hb _ ((mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t
      (fun g => l (.inr g))).mpr ⟨fun g k => h.1 (.inr g) k, fun g => h.2 (.inr g)⟩)
  have hwindow : sourceComparisonHighTimes (Real.log x*Y/H) ((Real.log x)^S) =
      {τ : ℝ | (Real.log x)^S ≤ |τ| ∧ |τ| ≤ T} := by
    rw [mul_div_assoc]
    ext τ
    change ((-T ≤ τ ∧ τ ≤ T) ∧ (Real.log x)^S ≤ |τ|) ↔ _
    rw [← abs_le]
    exact and_comm
  apply hjoin J u' hu q' hq' b' hb' Y σ hYlo hYhi hσ r hr T
  have hh := hhigh s i hout t ht q₀ hq₀ hq₀ρ q hq b hb Y H σ hYlo hYhi hHlo hHhi
    hσ r.den r.num hr
  rwa [hwindow] at hh

end
end ArtinMatthews
