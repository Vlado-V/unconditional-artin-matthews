module

public import ArtinMatthews.MarkedMinorArcCellBandwidth
public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedMinorArcRawProducts
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual support consequences of a nonzero clean raw edge. These recover
the physical squarefree shared product and finite cell-shift restriction
from the literal raw kernel rather than postulating its block support. -/
namespace ArtinMatthews
open Matrix

/-- A surviving endpoint has the full literal physical list restriction. -/
theorem markedRawEndpointFactor_ne_zero_distinct {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) (hs : markedRawEndpointFactor hZ ρ χ s ≠ 0) :
    MarkedRawActiveDistinct s.2.1 := by
  classical
  by_contra hd
  exact hs (by simp only [markedRawEndpointFactor,ite_eq_right hd])

/-- A nonzero actual edge retains the pad dyad, determinant congruence,
both full physical endpoints, and the genuine determinant cutoff. -/
theorem markedRawCleanKernel_ne_zero_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v ≠ 0) :
    (d₀ ≤ (markedRawCopiedProduct b.1 : ℝ) ∧ (markedRawCopiedProduct b.1 : ℝ) < 2*d₀) ∧
    (markedRawCopiedProduct b.1 : ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 ∧
    MarkedRawActiveDistinct ((markedRawStateSplit pads B Z).symm (b,u)).2.1 ∧
    MarkedRawActiveDistinct ((markedRawStateSplit pads B Z).symm (b,v)).2.1 ∧
    ψ (((markedMinorIntegerDet u.1.1 v.1.1/(markedRawCopiedProduct b.1 : ℤ) : ℤ) : ℝ)/Y) ≠ 0 := by
  classical
  dsimp only [markedRawCleanKernel] at h
  split_ifs at h with hdyad hdiv
  · simp only [mul_ne_zero_iff] at h
    exact ⟨hdyad,hdiv,
      markedRawEndpointFactor_ne_zero_distinct hZ ρ χ _ h.1.1.1.1.1.2,
      markedRawEndpointFactor_ne_zero_distinct hZ ρ χ _ h.2,h.1.1.2⟩
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

/-- Both actual endpoint multipliers survive on a nonzero raw edge. -/
theorem markedRawCleanKernel_ne_zero_endpoint_factors {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v ≠ 0) :
    markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,u)) ≠ 0 ∧
    markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (b,v)) ≠ 0 := by
  classical
  dsimp only [markedRawCleanKernel] at h
  split_ifs at h
  · simp only [mul_ne_zero_iff] at h
    exact ⟨h.1.1.1.1.1.2,h.2⟩
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

/-- The literal remaining test survives at every surviving endpoint. -/
theorem markedRawEndpointFactor_ne_zero_test {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) (hs : markedRawEndpointFactor hZ ρ χ s ≠ 0) : χ s ≠ 0 := by
  classical
  intro hz
  exact hs (by simp only [markedRawEndpointFactor,hz,mul_zero,ite_self])

/-- Actual physical endpoints force the shared copied product to be
squarefree on every nonzero raw clean edge. -/
theorem markedRawCleanKernel_ne_zero_squarefree {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v ≠ 0) :
    Squarefree (markedRawCopiedProduct b.1) := by
  have hs := (markedRawCleanKernel_ne_zero_support hZ ψ η d₀ Y Q ρ χ b u v h).2.2.1
  have hf := markedRawCopiedProduct_squarefree_of_fullDistinct hP pads _ hs
  change Squarefree (markedRawCopiedProduct
    (((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm (b.1,u.2))).1)) at hf
  simpa only [Equiv.apply_symm_apply] using hf

/-- The literal cutoff forces a uniformly finite set of actual cell shifts.
Its cardinality depends on the fixed cutoff and box lower bound alone. -/
theorem markedRawCleanKernel_ne_zero_shift {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    {d₀ Y c K : ℝ} (hd₀ : 0 < d₀) (hY : 0 < Y) (hc : 0 < c) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (r Q ρ : ℝ)
    (hτ : ∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z|)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (b : MarkedRawBackground P pads B)
    (u v : MarkedRawCleanFiber P Z)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ b u v ≠ 0) :
    markedMinorPositionCell r d₀ Y v.1.1-markedMinorPositionCell r d₀ Y u.1.1 ∈
      Finset.Icc (-(⌈2*K/c^2+1⌉₊ : ℤ)) (⌈2*K/c^2+1⌉₊ : ℤ) := by
  obtain ⟨hdyad,hdiv,_,_,hψnz⟩ := markedRawCleanKernel_ne_zero_support hZ ψ η d₀ Y Q ρ χ b u v h
  have hD : (0 : ℝ) < markedRawCopiedProduct b.1 := by exact_mod_cast markedRawCopiedProduct_pos b.1
  have harg := hψ hψnz
  have habs : |(((markedMinorIntegerDet u.1.1 v.1.1/(markedRawCopiedProduct b.1 : ℤ) : ℤ) : ℝ)/Y)| ≤ K :=
    abs_le.mpr harg
  have heq : (((markedMinorIntegerDet u.1.1 v.1.1/(markedRawCopiedProduct b.1 : ℤ) : ℤ) : ℝ))=
      (markedMinorIntegerDet u.1.1 v.1.1 : ℝ)/(markedRawCopiedProduct b.1 : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hD.ne' : (markedRawCopiedProduct b.1 : ℝ) ≠ 0)).mpr
    norm_cast
    exact Int.ediv_mul_cancel hdiv
  rw [heq,div_div,abs_div,abs_of_pos (mul_pos hD hY)] at habs
  have hdet := (div_le_iff₀ (mul_pos hD hY)).mp habs
  exact markedMinorPositionCell_shift_mem r hY hd₀ hc hK hD.le hdyad.2.le _ _
    (hτ _ u.1.2) (hτ _ v.1.2) (by nlinarith [hdet])

end ArtinMatthews
