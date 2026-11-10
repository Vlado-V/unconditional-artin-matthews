module

public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcDirtyMajorGeometry
public import ArtinMatthews.MarkedMinorArcDirtyMajorSupport
public import ArtinMatthews.MarkedMinorArcDirtyRawAnchor
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices
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

/-! The geometric count is instantiated from actual nonzero major edges,
with an actual promoted old index. No delta equation is used. -/
namespace ArtinMatthews
open Finset
noncomputable section

 theorem markedDirtyMajor_promoted_prime_not_dvd_shared {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (j : J) (k : Fin (s.2.2.1.1 j:ℕ)) (hk : choice.promotions j=some k)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ
      (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0) :
    ¬(((s.2.2.2 j k).1.1:ℕ):ℤ) ∣
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ) := by
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ s choice hne
  have hban : ∀ i l, (s.2.1 i l).1 ≠ (s.2.2.2 j k).1.1 := by
    intro i l
    have hh := markedDirtyEdgeCrossBan_prime_ne s.2.1 _ hs.2.2.1 i l j
    rwa [markedRawEdgeTargetLast_promoted s.2.2 choice.promotions choice.fresh j k hk] at hh
  have hfull := markedRawSourceFull_not_dvd_of_cross_ban s.2.1 (s.2.2.2 j k) hban
  intro hdiv
  apply hfull
  have heq : (markedSourceFullProduct (markedRawNumericActive s.2.1):ℤ)=
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ)*
      (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2:ℤ) := by
    exact_mod_cast markedRawFullProduct_split pads s.2.1
  rw [heq]
  exact dvd_mul_of_dvd_left hdiv _

 /-- Every actual nonzero target associated with a specified promoted old
particle is counted uniformly. Its gate, first-good shear, prime ban and
bounded determinant support are all extracted from the literal coefficient. -/
 theorem markedDirtyMajor_actual_targets_count {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) {c Bτ K : ℝ} (hY : 1 ≤ Y) (hc : 0 < c) (hBτ : 0 ≤ Bτ)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : Z → ℤ × ℤ) (hw : ∀ z,markedMinorIntegerDet z.1 (w z)=1)
    (hτ : ∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (j : J) (k : Fin (s.2.2.1.1 j:ℕ))
    (T : Finset (ℤ × ℤ)) (hTZ : T ⊆ Z)
    (hedges : ∀ v ∈ T,∃ choice : MarkedRawEdgeChoice hZ s,
      choice.target.1=v ∧ choice.promotions j=some k ∧
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0) :
    (T.card:ℝ) ≤ (300*(max 1 (max (Bτ/c) K))^2)*Y*
      (1/((s.2.2.2 j k).1.1:ℕ)+Y^(-1/10:ℝ)) := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨v₀,hv₀⟩ := hT
    obtain ⟨choice₀,_ht₀,hprom₀,hne₀⟩ := hedges v₀ hv₀
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
    have hD : 0 < D := markedRawCopiedProduct_pos _
    have hdiv : ∀ v ∈ T,(D:ℤ) ∣ markedMinorIntegerDet s.1.1 v := by
      intro v hv
      obtain ⟨choice,heq,_hprom,hne⟩ := hedges v hv
      have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ _ _ s choice hne
      simpa only [heq] using hs.2.1
    have hcut : ∀ v ∈ T, |(((markedMinorIntegerDet s.1.1 v/(D:ℤ):ℤ):ℝ))/Y| ≤ K := by
      intro v hv
      obtain ⟨choice,heq,_hprom,hne⟩ := hedges v hv
      have hn := markedDirtyMajor_cutoff_support hZ η ψ d₀ Y Q ρ _ s choice hne
      have hh := abs_le.mpr (hψ hn)
      simpa only [heq] using hh
    have hpoints := markedDirtyMajor_cutoff_points r (by linarith : 0 < Y) hc hBτ hD
      s.1.1 (w s.1) (hw s.1) (hτ _ s.1.2).1 T
      (fun v hv => (hτ v (hTZ hv)).2) hdiv hcut
    apply markedDirtyMajor_good_shared_count (s.2.2.2 j k) T (fun v hv => hZ v (hTZ hv)) hD
      s.1.1 (w s.1) (hw s.1) r hY (le_max_left _ _)
      (markedDirtyMajor_source_shear hZ η ψ r d₀ Y Q ρ w χ s choice₀ hne₀)
      (markedDirtyMajor_promoted_prime_not_dvd_shared hZ η ψ d₀ Y Q ρ _ s choice₀ j k hprom₀ hne₀)
      hdiv hpoints
    intro v hv
    obtain ⟨choice,heq,hprom,_hne⟩ := hedges v hv
    simpa only [heq] using choice.promotion_hits j k hprom
  · rw [not_nonempty_iff_eq_empty.mp hT,card_empty,Nat.cast_zero]
    positivity

end
end ArtinMatthews
