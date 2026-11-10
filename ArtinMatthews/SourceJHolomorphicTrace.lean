module

public import ArtinMatthews.SourceJHolomorphicModulus
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The complete odd correction equals the actual mixed-cusp all-even
Petersson Gram series. The exterior coefficient stays complex for both signs. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups ComplexConjugate
noncomputable section

private theorem norm_row_sums_summable {α β : Type*} (F : α → β → ℂ)
    (hF : Summable (fun p : α × β => ‖F p.1 p.2‖)) :
    Summable (fun a => ‖∑' b, F a b‖) := by
  obtain ⟨hrow,hsum⟩ := (summable_prod_of_nonneg (fun p : α × β => norm_nonneg (F p.1 p.2))).mp hF
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun a => norm_tsum_le_tsum_norm (hrow a)) hsum

def sourceJHolomorphicMixedGramTerm (f : ℝ → ℂ) (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) (j : ℕ) : ℂ :=
  spectralJHolomorphicCoefficient f (2*j+2)*
    gamma0PeterssonInner (r*s) (2*j+2)
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab (2*j+2) n))
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity (r*s) (2*j+2) m))

def sourceJHolomorphicMixedGramSeries (f : ℝ → ℂ) (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) : ℂ :=
  ∑' j : ℕ, sourceJHolomorphicMixedGramTerm f r s hab negative m n j

theorem sourceJHolomorphicMixedGramTerm_modulus (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) (j : ℕ) :
    sourceJHolomorphicMixedGramTerm f r s hab negative m n j =
      ∑' c : Ioi (0 : ℕ), spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1
          (2*j+2) negative m n c := by
  have he : Even (2*j+2) := ⟨j+1,by omega⟩
  unfold sourceJHolomorphicMixedGramTerm
  rw [(gamma0PeterssonSourceMixed_signed_gram r s hr hcop hab (2*j+2) (by omega) he negative m n).2]
  rw [tsum_mul_left]

theorem sourceJHolomorphicMixedGramTerm_zero (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) :
    sourceJHolomorphicMixedGramTerm f r s hab negative m n 0 =
      (-spectralJDiscreteCoefficient f 1/(Real.pi : ℂ))*
        gamma0PeterssonInner (r*s) 2
          (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab 2 n))
          (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity (r*s) 2 m)) := by
  simp only [sourceJHolomorphicMixedGramTerm,mul_zero,zero_add,spectralJHolomorphicCoefficient_two]

theorem sourceJHolomorphicMixedGramTerm_summable (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) :
    Summable (fun j : ℕ => ‖sourceJHolomorphicMixedGramTerm f r s hab negative m n j‖) := by
  have hs := sourceJHolomorphicCoefficient_signed_joint_summable f hf hc hp
    (r*s) (gamma0CuspOneOver s) negative m n
  have hh := norm_row_sums_summable
    (fun j c => spectralJHolomorphicCoefficient f (2*j+2)*
      gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 (2*j+2) negative m n c) hs
  exact hh.congr fun j => congrArg norm (sourceJHolomorphicMixedGramTerm_modulus f r s hr hcop hab negative m n j).symm

theorem sourceJHolomorphicOdd_geometric_summable (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (negative : Bool) (m n : ℕ+) :
    Summable (fun c : Ioi (0 : ℕ) => ‖gamma0ABLOppositeGeometricTerm N b 1 c
      (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)
      (spectralJOddSynthesis f)‖) := by
  have hs := (sourceJHolomorphicCoefficient_signed_joint_summable f hf hc hp N b negative m n).prod_symm
  have hh := norm_row_sums_summable
    (fun c j => spectralJHolomorphicCoefficient f (2*j+2)*
      gamma0PeterssonSignedGramModulusTerm N b 1 (2*j+2) negative m n c) hs
  exact hh.congr fun c => congrArg norm (sourceJHolomorphicCoefficient_signed_modulus_sum f N b 1 negative m n c)

theorem sourceJHolomorphicMixedGramSeries_eq_odd (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) :
    sourceJHolomorphicMixedGramSeries f r s hab negative m n =
      ∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm (r*s) (gamma0CuspOneOver s) 1 c
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative m)
        (spectralJOddSynthesis f) := by
  have hs := (sourceJHolomorphicCoefficient_signed_joint_summable f hf hc hp
    (r*s) (gamma0CuspOneOver s) negative m n).of_norm
  calc
    _ = ∑' j : ℕ, ∑' c : Ioi (0 : ℕ), spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 (2*j+2) negative m n c :=
      tsum_congr fun j => sourceJHolomorphicMixedGramTerm_modulus f r s hr hcop hab negative m n j
    _ = ∑' c : Ioi (0 : ℕ), ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 (2*j+2) negative m n c := hs.tsum_comm.symm
    _ = _ := tsum_congr fun c => sourceJHolomorphicCoefficient_signed_modulus_sum f (r*s)
      (gamma0CuspOneOver s) 1 negative m n c

end
end ArtinMatthews
