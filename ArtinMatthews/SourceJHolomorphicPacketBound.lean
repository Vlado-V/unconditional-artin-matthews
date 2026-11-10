module

public import ArtinMatthews.SpectralPeterssonSourceDensity
public import ArtinMatthews.SourceJHolomorphicHilbert
public import ArtinMatthews.SourceJHolomorphicSignedNorm
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

/-! The actual all-even density bounds give Cauchy--Schwarz for the
literal signed source packet and its normalized mixed singleton. -/
namespace ArtinMatthews
open Set
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section

theorem sourceJHolomorphicInfinityPacketL2_density {ι : Type*} (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) {B : ℝ} (hB : 0 < B)
    (hm : Set.InjOn m (v : Set ι)) (hmB : ∀ i ∈ v, (m i : ℝ) ≤ B) :
    ‖sourceJHolomorphicInfinityPacketL2 N k hk hEven negative v α m‖^2 ≤
      spectralPeterssonDensityConstant*(1+B/(N : ℝ))*(∑ i ∈ v, ‖α i‖^2) := by
  rw [sourceJHolomorphicInfinityPacketL2_norm_sq_integral]
  have h := gamma0PeterssonSourceInfinityPacket_uniform_density N k hk hEven v
    (fun i => if negative then conj (α i) else α i) m hB hm hmB
  have hsum : (∑ i ∈ v, ‖if negative then conj (α i) else α i‖^2) = ∑ i ∈ v, ‖α i‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    cases negative <;> simp
  rw [hsum] at h
  exact h

theorem sourceJHolomorphicAtkinL2_density
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (negative : Bool) (n : ℕ+) :
    ‖gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n‖^2 ≤
      spectralPeterssonDensityConstant*(1+(n : ℝ)/((r*s : ℕ) : ℝ)) := by
  rw [sourceJHolomorphicAtkinL2_norm_sq_integral]
  exact gamma0PeterssonSourceAtkin_uniform_density r s hcop hab k hk hEven n

theorem sourceJHolomorphicMixedPacket_inner_bound {ι : Type*}
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+)
    {B : ℝ} (hB : 0 < B) (hm : Set.InjOn m (v : Set ι)) (hmB : ∀ i ∈ v, (m i : ℝ) ≤ B) :
    ‖⟪gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n,
      sourceJHolomorphicInfinityPacketL2 (r*s) k hk hEven negative v α m⟫_ℂ‖ ≤
      spectralPeterssonDensityConstant*
        Real.sqrt ((∑ i ∈ v, ‖α i‖^2)*(1+B/((r*s : ℕ) : ℝ)))*
        Real.sqrt (1+(n : ℝ)/((r*s : ℕ) : ℝ)) := by
  let D := spectralPeterssonDensityConstant
  let N := ((r*s : ℕ) : ℝ)
  let U := (∑ i ∈ v, ‖α i‖^2)*(1+B/N)
  let V := 1+(n : ℝ)/N
  let A := gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n
  let P := sourceJHolomorphicInfinityPacketL2 (r*s) k hk hEven negative v α m
  have hD : 0 ≤ D := spectralPeterssonDensityConstant_pos.le
  have ha : ‖A‖^2 ≤ D*V := sourceJHolomorphicAtkinL2_density r s hcop hab k hk hEven negative n
  have hp : ‖P‖^2 ≤ D*U :=
    (sourceJHolomorphicInfinityPacketL2_density (r*s) k hk hEven negative v α m hB hm hmB).trans_eq (by
      dsimp only [D,U,N]
      ring)
  have ha' : ‖A‖ ≤ Real.sqrt D*Real.sqrt V := by
    rw [← Real.sqrt_mul hD]
    exact (Real.sqrt_sq (norm_nonneg A)).symm.le.trans (Real.sqrt_le_sqrt ha)
  have hp' : ‖P‖ ≤ Real.sqrt D*Real.sqrt U := by
    rw [← Real.sqrt_mul hD]
    exact (Real.sqrt_sq (norm_nonneg P)).symm.le.trans (Real.sqrt_le_sqrt hp)
  change ‖⟪A,P⟫_ℂ‖ ≤ D*Real.sqrt U*Real.sqrt V
  calc
    _ ≤ ‖A‖*‖P‖ := norm_inner_le_norm _ _
    _ ≤ (Real.sqrt D*Real.sqrt V)*(Real.sqrt D*Real.sqrt U) :=
      mul_le_mul ha' hp' (norm_nonneg _) (by positivity)
    _ = (Real.sqrt D)^2*Real.sqrt U*Real.sqrt V := by ring
    _ = _ := by rw [Real.sq_sqrt hD]

theorem sourceJHolomorphicMixedPacketTerm_norm_bound {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+)
    {B : ℝ} (hB : 0 < B) (hm : Set.InjOn m (v : Set ι)) (hmB : ∀ i ∈ v, (m i : ℝ) ≤ B)
    (j : ℕ) :
    ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖ ≤
      ‖spectralJHolomorphicCoefficient f (2*j+2)‖*
        (spectralPeterssonDensityConstant*
          Real.sqrt ((∑ i ∈ v, ‖α i‖^2)*(1+B/((r*s : ℕ) : ℝ)))*
          Real.sqrt (1+(n : ℝ)/((r*s : ℕ) : ℝ))) := by
  have he : Even (2*j+2) := ⟨j+1,by omega⟩
  have hi := sourceJHolomorphicMixedPacket_inner_bound r s hcop hab
    (2*j+2) (by omega) he negative v α m n hB hm hmB
  rw [sourceJHolomorphicMixedPacketTerm_eq_inner f r s hcop hab negative v α m n j,norm_mul]
  exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

end
end ArtinMatthews
