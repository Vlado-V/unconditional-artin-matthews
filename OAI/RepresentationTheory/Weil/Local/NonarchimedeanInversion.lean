module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.CompactCharacter
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.MetricSpace.Ultra.Pi
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Nonarchimedean Inversion -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanInversion.Construction

noncomputable section

/-! Compact frequency domains adapted to nonarchimedean test functions. -/

open _root_.MeasureTheory
open scoped Classical

theorem additiveAnnihilator_small
    {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : k) (ha : ψ a ≠ 1)
    (U : AddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (ε R : ℝ) (hε : 0 < ε)
    (hR : ‖a‖ / ε ≤ R)
    (hU : Metric.closedBall (0 : FunctionsMetaplectic.Construction.Position k n) R ⊆ U) :
    ∀ x ∈ CompactCharacter.Construction.additiveAnnihilator ψ U, ‖x‖ < ε := by
  intro x hx
  apply (pi_norm_lt_iff hε).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hε.trans_le hi)
  let t : FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : t ∈ U := by
    apply hU
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(Pi.single i (a / x i) : FunctionsMetaplectic.Construction.Position k n)‖ ≤ R
    rw [Pi.norm_single, norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hε hi).trans hR
  have hdot : FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  apply ha
  have h := hx t ht
  rwa [hdot] at h

theorem exists_adapted_frequency_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n), IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) ∧
      tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U ∧
      ∀ t ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, f (x + t) = f x := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  have hF := CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μ hf hs
  obtain ⟨R, hR, hbound⟩ := hF.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, heq⟩ := CompactCharacter.Construction.compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hn
  let S : ℝ := max R (‖a‖ / ε) + 1
  have hS : 0 < S := by
    exact lt_trans hR (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) hS
  have hUS : (U : Set (FunctionsMetaplectic.Construction.Position k n)) = Metric.closedBall 0 S := rfl
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUS]
    exact isCompact_closedBall _ _
  · intro x hx
    rw [hUS, Metric.mem_closedBall, dist_zero_right]
    exact (hbound x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  · intro t ht x
    apply heq x t
    apply additiveAnnihilator_small ψ a ha U.toAddSubgroup ε S hε _ _ t ht
    · exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    · exact fun _ hx => hx

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanInversion.Construction
