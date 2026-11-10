module

public import ArtinMatthews.SpectralPeterssonGram
public import ArtinMatthews.SpectralWeylPlanarCoordinates
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual both-negative terms are obtained from the conjugate
Petersson vectors. No conjugation is applied to an exterior test weight. -/

noncomputable section
open Matrix Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem gamma0PeterssonInner_conj (N k : ℕ) (F G : UpperHalfPlane → ℂ) :
    gamma0PeterssonInner N k (fun z => conj (F z)) (fun z => conj (G z)) =
      conj (gamma0PeterssonInner N k F G) := by
  unfold gamma0PeterssonInner
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with z
  unfold UpperHalfPlane.petersson
  simp only [map_mul,zpow_natCast,map_pow,Complex.conj_ofReal,Complex.conj_conj]

theorem gamma0TrueWidthKloostermanSum_both_neg (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (c : ℕ) [NeZero c] (m n : ℤ) :
    gamma0TrueWidthKloostermanSum N b a c (-n) (-m) = conj (gamma0TrueWidthKloostermanSum N b a c n m) := by
  unfold gamma0TrueWidthKloostermanSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro R _
  unfold cuspTrueWidthGeometricPhase
  have hphase (t : ℝ) : conj (atkinPhase t) = atkinPhase (-t) := atkinPhase_conj t
  rw [hphase]
  congr 1
  push_cast
  ring

theorem spectralPetersson_besselJ_nat_conj (l : ℕ) (x : ℝ) :
    conj (Complex.besselJ (l : ℂ) (x : ℂ)) = Complex.besselJ (l : ℂ) (x : ℂ) := by
  rw [spectralPetersson_besselJ_nat_factorial,map_mul,map_pow,Complex.conj_tsum]
  simp only [map_mul,map_div₀,map_pow,map_neg,map_natCast,map_ofNat,Complex.conj_ofReal]

theorem spectralPetersson_I_negWeight_conj (k : ℕ) (hEven : Even k) :
    conj (Complex.I^(-(k : ℤ))) = Complex.I^(-(k : ℤ)) := by
  simp only [_root_.zpow_neg,zpow_natCast,map_inv₀,map_pow,Complex.conj_I,hEven.neg_pow]

def gamma0PeterssonNegativeGramModulusTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N b a c.val (-(n : ℤ)) (-(m : ℤ))*
    (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ))*
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)

theorem gamma0PeterssonNegativeGramModulusTerm_eq_conj (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hEven : Even k) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    gamma0PeterssonNegativeGramModulusTerm N b a k m n c = conj (gamma0PeterssonGramModulusTerm N b a k m n c) := by
  unfold gamma0PeterssonNegativeGramModulusTerm gamma0PeterssonGramModulusTerm
  dsimp only
  rw [gamma0TrueWidthKloostermanSum_both_neg]
  simp only [map_mul,map_div₀,map_ofNat,Complex.conj_ofReal,spectralPetersson_I_negWeight_conj k hEven,
    spectralPetersson_besselJ_nat_conj]

theorem gamma0PeterssonInner_negative_of_positive (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hEven : Even k) (m n : ℕ+) (F G : UpperHalfPlane → ℂ) (d : ℝ)
    (hs : Summable (gamma0PeterssonGramModulusTerm N b a k m n))
    (h : gamma0PeterssonInner N k F G = (d : ℂ)+∑' c, gamma0PeterssonGramModulusTerm N b a k m n c) :
    Summable (gamma0PeterssonNegativeGramModulusTerm N b a k m n) ∧
      gamma0PeterssonInner N k (fun z => conj (F z)) (fun z => conj (G z)) =
        (d : ℂ)+∑' c, gamma0PeterssonNegativeGramModulusTerm N b a k m n c := by
  refine ⟨?_,?_⟩
  · apply Summable.of_norm
    simpa only [gamma0PeterssonNegativeGramModulusTerm_eq_conj N b a k hEven m n,Complex.norm_conj] using hs.norm
  · rw [gamma0PeterssonInner_conj,h,map_add,Complex.conj_ofReal,Complex.conj_tsum]
    simp only [gamma0PeterssonNegativeGramModulusTerm_eq_conj N b a k hEven m n]

theorem gamma0PeterssonNormalized_negative_inequivalent_gram (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (h : ¬ gamma0EisensteinCuspsEquivalent N b a) (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) :
    Summable (gamma0PeterssonNegativeGramModulusTerm N b a k m n) ∧
      gamma0PeterssonInner N k (fun z => conj (gamma0PeterssonNormalized N b k n z))
        (fun z => conj (gamma0PeterssonNormalized N a k m z)) =
        ∑' c, gamma0PeterssonNegativeGramModulusTerm N b a k m n c := by
  obtain ⟨hs,hGram⟩ := gamma0PeterssonNormalized_inequivalent_gram N b a h k hk hEven m n
  simpa only [Complex.ofReal_zero,zero_add] using
    gamma0PeterssonInner_negative_of_positive N b a k hEven m n _ _ 0 hs (by simpa using hGram)

theorem gamma0PeterssonNormalized_negative_same_cusp_gram (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) :
    Summable (gamma0PeterssonNegativeGramModulusTerm N a a k m n) ∧
      gamma0PeterssonInner N k (fun z => conj (gamma0PeterssonNormalized N a k n z))
        (fun z => conj (gamma0PeterssonNormalized N a k m z)) =
        (if m=n then 1 else 0)+∑' c, gamma0PeterssonNegativeGramModulusTerm N a a k m n c := by
  obtain ⟨hs,hGram⟩ := gamma0PeterssonNormalized_same_cusp_gram N a k hk hEven m n
  have hD : (((if m=n then 1 else 0) : ℝ) : ℂ) = (if m=n then 1 else 0) := by split_ifs <;> simp
  have H := gamma0PeterssonInner_negative_of_positive N a a k hEven m n _ _
    (if m=n then 1 else 0) hs (by rwa [hD])
  simpa only [hD] using H

end ArtinMatthews
