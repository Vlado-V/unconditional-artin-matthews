module

public import ArtinMatthews.GiantComparisonArcMellin
public import ArtinMatthews.GiantComparisonCutoffRows
public import ArtinMatthews.GiantComparisonEndpointGlobalMoment
public import ArtinMatthews.GiantComparisonMellinTail
public import ArtinMatthews.GiantComparisonArcCore
public import ArtinMatthews.GiantComparisonDistinguishedArcEnergy
public import ArtinMatthews.SourceComparisonDistinguishedReindex
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

/-! A performed-small group supplies the distinguished mark in the
full arc estimate on the original group family. -/
namespace ArtinMatthews

open Filter MeasureTheory Set
open scoped ContDiff
noncomputable section

universe u v
variable {I : Type u} [Fintype I]

theorem giantComparisonActualArcEnergy_eventually
    (e : I → ℝ) (he : ∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5)
    (hinj : Function.Injective e) (m : ℕ) {ρ : ℝ} (hρ : (1/2 : ℝ) ≤ ρ) (hρ₁ : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {lo hi B : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (hB : hi < B)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Icc lo hi)
    (C D A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] [DecidableEq G]
      (i : G ↪ GiantCandidateGroupIndex x)
      (g : G) (s : GiantCandidateSmallGroupIndex x), i g = Sum.inl s →
      ∀ (t : G → ℕ), (∀ j, t j ≤ m) → t g = 1 →
      ∀ (q : G → ℝ), (∀ j, 0 ≤ q j ∧ q j ≤ ρ) →
      ∀ (b : ((j : G) → Fin (t j) → ℕ) → ℂ),
        (∀ l, ‖b l‖ ≤ 1) →
        (∀ l l', (∀ j, j ≠ g → l j = l' j) → b l = b l') →
      ∀ (Y H σ : ℝ), x ≤ Y → Y ≤ x ^ (1 + ε/4) →
        Real.exp ((Real.log x)^(38/100 : ℝ)) ≤ H → H ≤ Real.exp (Real.log x/2) →
        |σ| ≤ (Real.log x)^D →
      ∀ (r : ℚ), (r.den : ℝ) ≤ (Real.log x)^C →
      let T := Real.log x*(Y/H)
      (∫ τ in Icc (-T) T, ‖(Y : ℂ)⁻¹ *
        giantComparisonMellinPolynomial (giantComparisonCutoffRows Y lo hi)
          (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ
            (giantCandidateGroup x ∘ i) t q b)) τ‖ ^ 2) ≤ (Real.log x)^(-A) := by
  filter_upwards [giantComparisonDistinguishedArcEnergy_eventually.{u,v}
    e he hinj m hρ hρ₁ hε hεq hlo hlohi hB ψ hψ hs C D A hC hA,
    eventually_ge_atTop (1 : ℝ)] with x harc hx
  intro G _ _ i g s hg t ht ht₀ q hq b hb hbind Y H σ hYlo hYhi hHlo hHhi hσ r hr
  let _ : NeZero r.den := ⟨r.den_ne_zero⟩
  let i' := sourceComparisonOtherGroupEmbedding i g
  let hout := sourceComparisonOtherGroupEmbedding_outside i g s hg
  let i'' := sourceComparisonDistinguishedGroupEmbedding s i' hout
  let t' (j : {j : G // j ≠ g}) := t j
  let q' (j : {j : G // j ≠ g}) := q j
  let b' := sourceComparisonOtherMarkTest t g b 0
  let P := giantCandidateGroup x ∘ i
  let P' := giantCandidateGroup x ∘ i''
  let u' : Unit ⊕ {j : G // j ≠ g} → ℕ := Sum.elim (fun _ => 1) t'
  let r' : Unit ⊕ {j : G // j ≠ g} → ℝ := Sum.elim (fun _ => q g) q'
  let b'' (l : (j : Unit ⊕ {j : G // j ≠ g}) → Fin (u' j) → ℕ) := b' (fun j => l (.inr j))
  let T := Real.log x*(Y/H)
  have hY : 0 < Y := zero_lt_one.trans_le (hx.trans hYlo)
  have hb' (l : (j : {j : G // j ≠ g}) → Fin (t' j) → ℕ) : ‖b' l‖ ≤ 1 := hb _
  let f (τ : ℝ) := (Y : ℂ)⁻¹ * giantComparisonMellinPolynomial
    (giantComparisonCutoffRows Y lo hi)
    (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ P t q b)) τ
  let f' (τ : ℝ) := (Y : ℂ)⁻¹ * giantComparisonMellinPolynomial
    (giantComparisonCutoffRows Y lo hi)
    (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ P' u' r' b'')) τ
  have heq : f = f' := by
    funext τ
    calc
      _ = sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b r.den r.num τ :=
        giantComparisonArcCore_eq_centeredMellinSum e ε x σ τ ψ P t q b r hY hB.le hs
      _ = sourceComparisonCenteredMellinSum e ε x Y σ B ψ P' u' r' b'' r.den r.num τ :=
        sourceComparisonCenteredMellinSum_distinguish e ε x Y σ B ψ i g s hg t ht₀ q b hbind 0
          r.den r.num τ
      _ = _ := (giantComparisonArcCore_eq_centeredMellinSum e ε x σ τ ψ P' u' r' b'' r hY hB.le hs).symm
  change (∫ τ in Icc (-T) T, ‖f τ‖ ^ 2) ≤ (Real.log x)^(-A)
  rw [heq]
  exact harc s i' hout t' (fun j => ht j) (q g) (hq g).1 (hq g).2 q' (fun j => hq j)
    b' (fun l _ => hb' l) Y H σ hYlo hYhi hHlo hHhi hσ r hr

end
end ArtinMatthews
