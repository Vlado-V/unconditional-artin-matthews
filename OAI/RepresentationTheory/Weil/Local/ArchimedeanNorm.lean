module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.Coordinates
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
public import Mathlib.NumberTheory.Ostrowski
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

/-! # Archimedean Norm -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm.Construction

noncomputable section

/-! The chosen norm at an archimedean place is a positive power of the ordinary absolute value. -/

theorem realEmbedding_norm_power
    (k : Type) [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ x : ℝ, ‖Coordinates.Construction.realEmbeddingOfUnbounded k h x‖ = |x| ^ s := by
  have hh : ¬ ∀ n : ℕ, Coordinates.Construction.rationalNorm k n ≤ 1 := by simpa [Coordinates.Construction.rationalNorm] using h
  have he := Rat.AbsoluteValue.equiv_real_of_unbounded hh
  obtain ⟨s, hs, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he.symm
  have hp (q : ℚ) : ‖(q : k)‖ = ‖q‖ ^ s := by
    have hq := congrFun heq q
    simpa [Coordinates.Construction.rationalNorm, Rat.AbsoluteValue.real_eq_abs, ← Real.norm_eq_abs,
      Rat.norm_cast_real] using hq.symm
  have hc : Continuous (fun x : ℝ => ‖x‖ ^ s) := continuous_norm.rpow_const (fun _ => Or.inr hs.le)
  have H := Rat.denseRange_cast.equalizer
    (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h).norm hc
    (show (fun x : ℝ => ‖Coordinates.Construction.realEmbeddingOfUnbounded k h x‖) ∘ (Rat.castHom ℝ) =
      (fun x : ℝ => ‖x‖ ^ s) ∘ (Rat.castHom ℝ) from by
        funext q
        change ‖Coordinates.Construction.realEmbeddingOfUnbounded k h (q : ℝ)‖ = ‖(q : ℝ)‖ ^ s
        rw [map_ratCast, Rat.norm_cast_real]
        exact hp q)
  have h2 : ‖(2 : k)‖ ≤ (2 : ℝ) := by
    calc
      _ = ‖(1 : k) + 1‖ := by congr 1; norm_num
      _ ≤ ‖(1 : k)‖ + ‖(1 : k)‖ := norm_add_le _ _
      _ = 2 := by norm_num
  have hp2 : ‖(2 : k)‖ = (2 : ℝ) ^ s := by
    simpa only [map_ofNat, Real.norm_ofNat] using congrFun H 2
  refine ⟨s, hs, ?_, fun x => ?_⟩
  · apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
    rw [Real.rpow_one, ← hp2]
    exact h2
  · simpa only [Real.norm_eq_abs] using congrFun H x

theorem continuous_real_embedding_unique
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℝ →+* k) (he : Continuous e) :
    e = Coordinates.Construction.realEmbeddingOfUnbounded k h := by
  apply RingHom.ext
  have H := Rat.denseRange_cast.equalizer he (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h)
    (show e ∘ (Rat.castHom ℝ) = Coordinates.Construction.realEmbeddingOfUnbounded k h ∘ (Rat.castHom ℝ) from by
      funext q
      change e (q : ℝ) = Coordinates.Construction.realEmbeddingOfUnbounded k h (q : ℝ)
      rw [map_ratCast, map_ratCast])
  exact congrFun H

theorem continuous_real_embedding_norm_power
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℝ →+* k) (he : Continuous e) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ x : ℝ, ‖e x‖ = |x| ^ s := by
  rw [continuous_real_embedding_unique h e he]
  exact realEmbedding_norm_power k h

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm.Construction
