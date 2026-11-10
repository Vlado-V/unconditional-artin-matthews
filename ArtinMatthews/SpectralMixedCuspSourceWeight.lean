module

public import ArtinMatthews.SpectralMixedCuspKloostermanWeil
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedCuspSourcePhase
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

/-! The exact weighted finite mixed-cusp sum in ABL Theorem 2.4,
including the source's inverse-s phase and normalized-modulus weight. -/

noncomputable section
open scoped MatrixGroups BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem gamma0MixedKloosterman_source_weighted_standard (r s c : ℕ)
    [NeZero r] [NeZero s] [NeZero c] (hcop : r.Coprime s) (hrc : r.Coprime c) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    let hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    (((s : ℝ)*Real.sqrt (r : ℝ)/gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (s*c : ℕ) : ℝ) : ℂ)*
        (atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))*
          gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c) n m) =
      (1/(c : ℂ))*standardSum (s*c) (m*spectral_inverseUnitRepresentative r (s*c) hrq) n := by
  dsimp only
  rw [gamma0MixedCusp_trueModulus r s hcop,
    atkinMixed_modulus_weight (NeZero.pos r) (NeZero.pos s) (NeZero.pos c),
    gamma0MixedKloosterman_source_compensation r s c hcop hrc hab,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast,standardSum,
    Int.cast_mul,spectral_inverseUnitRepresentative_cast]

theorem gamma0MixedKloosterman_source_weighted_finite_sum (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (n : ℤ)
    (T : Finset {c : ℕ // 0 < c ∧ r.Coprime c}) (J : Finset ℤ)
    (α : ℤ → ℂ) (F : ℤ → ℕ → ℂ) :
    (∑ c ∈ T,
      letI : NeZero c.val := ⟨c.property.1.ne'⟩
      (((s : ℝ)*Real.sqrt (r : ℝ)/
          gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (s*c.val : ℕ) : ℝ) : ℂ)*
        ∑ m ∈ J, α m*F m c.val*
          (atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))*
            gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c.val) n m)) =
    ∑ c ∈ T,
      letI : NeZero c.val := ⟨c.property.1.ne'⟩
      let hrq : r.Coprime (s*c.val) := Nat.coprime_mul_iff_right.mpr ⟨hcop,c.property.2⟩
      (1/(c.val : ℂ))*∑ m ∈ J, α m*F m c.val*
        standardSum (s*c.val) (m*spectral_inverseUnitRepresentative r (s*c.val) hrq) n := by
  apply Finset.sum_congr rfl
  intro c _
  let _ : NeZero c.val := ⟨c.property.1.ne'⟩
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h := gamma0MixedKloosterman_source_weighted_standard r s c.val hcop c.property.2 hab m n
  dsimp only at h
  linear_combination α m*F m c.val*h

end ArtinMatthews
