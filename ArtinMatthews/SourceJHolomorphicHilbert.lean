module

public import ArtinMatthews.SourceJHolomorphicPacket
public import ArtinMatthews.SpectralPeterssonSourceHilbert
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

/-! The all-even source trace and its finite packet are literal inner
products of the checked signed source vectors in the native Petersson L² space. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators InnerProductSpace
noncomputable section

private theorem sourceJ_weight_even (j : ℕ) : Even (2*j+2) := ⟨j+1,by omega⟩

private theorem sourceJ_weight_lower (j : ℕ) : 2 ≤ 2*j+2 := by omega

def sourceJHolomorphicInfinityPacketL2 {ι : Type*} (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) : Gamma0PeterssonL2 N :=
  ∑ i ∈ v, α i • gamma0PeterssonSourceInfinityL2 N k hk hEven negative (m i)

theorem sourceJHolomorphicMixedGramSeries_eq_hilbert (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) :
    sourceJHolomorphicMixedGramSeries f r s hab negative m n =
      ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          gamma0PeterssonSourceInfinityL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative m⟫_ℂ := by
  apply tsum_congr
  intro j
  rw [gamma0PeterssonSourceL2_mixed_inner]
  rfl

theorem sourceJHolomorphicMixedPacketTerm_eq_inner {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) (j : ℕ) :
    sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j =
      spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          sourceJHolomorphicInfinityPacketL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative v α m⟫_ℂ := by
  unfold sourceJHolomorphicInfinityPacketL2
  rw [inner_sum]
  simp_rw [inner_smul_right,gamma0PeterssonSourceL2_mixed_inner]
  rfl

theorem sourceJHolomorphicMixedPacketSeries_eq_hilbert {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    sourceJHolomorphicMixedPacketSeries f r s hab negative v α m n =
      ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          sourceJHolomorphicInfinityPacketL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative v α m⟫_ℂ := by
  apply tsum_congr
  intro j
  exact sourceJHolomorphicMixedPacketTerm_eq_inner f r s hcop hab negative v α m n j

end
end ArtinMatthews
