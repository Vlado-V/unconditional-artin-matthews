module

public import ArtinMatthews.SpectralKFrameCompactProfiles
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The same compact K frame controls finite nonnegative spectral
moments on its band. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem spectralKFrame_principal_finset_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (u : Finset ι) (t A : ι → ℝ) (T V : ℝ),
      (1/2 : ℝ) ≤ T → 0 ≤ V → (∀ i ∈ u, 0 ≤ A i) →
      (∀ i ∈ u, T ≤ 1+|t i| ∧ 1+|t i| ≤ 2*T) →
      (∀ F : ℝ → ℝ, spectralKFrameProfileBound T F →
        (∑ i ∈ u, A i*‖spectralCompactRealKTransform F (t i)‖^2) ≤ V*spectralKFrameLength) →
      (∑ i ∈ u, A i/Real.cosh (Real.pi*t i)) ≤ C*T^2*V := by
  let L := spectralKFrameLength
  let P := Real.pi^2*L/5184
  have hL : 0 < L := spectralKFrameLength_pos
  have hP : 0 < P := by dsimp only [P]; positivity
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_exists_compact_phase_profiles
  refine ⟨2*C*L/P,by positivity,?_⟩
  intro ι u t A T V hhalf hV hA hband hMom
  have hT : 0 < T := by linarith
  obtain ⟨modes,F,G,hcard,hProfiles,hLower⟩ := hFrame T hhalf
  let K (F₀ : ℝ → ℝ) (i : ι) := ‖spectralCompactRealKTransform F₀ (t i)‖^2
  let E (m : ℤ) (i : ι) := A i*K (F m) i+A i*K (G m) i
  have hE (m : ℤ) : (∑ i ∈ u, E m i) ≤ 2*V*L := by
    simp only [E,K,Finset.sum_add_distrib]
    exact (add_le_add (hMom _ (hProfiles m).1) (hMom _ (hProfiles m).2)).trans_eq (by
      dsimp only [L]
      ring)
  have hTotal : (∑ i ∈ u, ∑ m ∈ modes, E m i) ≤ (C*T)*(2*V*L) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _m ∈ modes, 2*V*L := Finset.sum_le_sum (fun m _ => hE m)
      _ = (modes.card : ℝ)*(2*V*L) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hRow (i : ι) (hi : i ∈ u) :
      P/T*(A i/Real.cosh (Real.pi*t i)) ≤ ∑ m ∈ modes, E m i := by
    calc
      _ = A i*(P/(T*Real.cosh (Real.pi*t i))) := by ring
      _ ≤ A i*(∑ m ∈ modes, (K (F m) i+K (G m) i)) :=
        mul_le_mul_of_nonneg_left (hLower (t i) (hband i hi).1 (hband i hi).2) (hA i hi)
      _ = _ := by simp only [E,Finset.mul_sum,mul_add]
  apply (mul_le_mul_iff_of_pos_left (div_pos hP hT)).mp
  calc
    _ ≤ ∑ i ∈ u, ∑ m ∈ modes, E m i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hRow
    _ ≤ (C*T)*(2*V*L) := hTotal
    _ = _ := by field_simp [hP.ne',hT.ne']

end ArtinMatthews
