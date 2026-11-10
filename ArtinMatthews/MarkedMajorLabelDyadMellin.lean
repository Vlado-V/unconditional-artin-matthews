module

public import ArtinMatthews.MarkedMajorLabelCofactor
public import ArtinMatthews.MarkedMajorMellinIsolationBase
public import ArtinMatthews.MarkedMajorPrimeDyads
public import ArtinMatthews.MarkedMajorLabelMellin
public import ArtinMatthews.MarkedMajorLabelSplit
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The exact normalized dyad contribution to the full prime-label
polynomial, and its actual absolutely convergent Mellin factorization. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped ContDiff

noncomputable def markedMajorLabelDyad {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (S : Finset ℕ) (η : ℝ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (θ Y V t : ℝ) : ℂ :=
  (V:ℂ)⁻¹*(Y:ℂ)⁻¹*∑ p ∈ S,∑ n ∈ markedMajorLabelSet P,
    (η ((p*n:ℕ)/Y)*Complex.exp (-(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ))))*
      ((markedMajorLabelMass P:ℂ)*χ (p*n))*markedPrimePhase (p*n) t

theorem markedMajorLabelDyad_mellin {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (S : Finset ℕ) (hS : ∀ p ∈ S,0 < p)
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Set.Icc a b)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (θ Y H V t : ℝ)
    (hY : 0 < Y) (hH : 0 < H)
    (hlo : ∀ p ∈ S,H ≤ (p:ℝ)) (hhi : ∀ p ∈ S,(p:ℝ) ≤ 2*H) :
    markedMajorLabelDyad P S η χ θ Y V t = (V:ℂ)⁻¹*
      ∫ ξ : ℝ,markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
        (Complex.exp (-(Complex.I*(ξ:ℂ)*(Real.log Y:ℂ)))*
          markedPrimePolynomial S H χ ξ t*
          markedMajorCofactorPolynomial P (markedMajorCofactorSet P a b Y H) χ Y H (t+ξ)) := by
  classical
  let R := markedMajorCofactorSet P a b Y H
  have hR : ∀ n ∈ R,0 < n := fun n hn => markedMajorLabelSet_pos P hP (mem_filter.mp hn).1
  have hrestrict :
      (∑ p ∈ S,∑ n ∈ markedMajorLabelSet P,
        (η ((p*n:ℕ)/Y)*Complex.exp (-(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ))))*
          ((markedMajorLabelMass P:ℂ)*χ (p*n))*markedPrimePhase (p*n) t) =
      ∑ p ∈ S,∑ n ∈ R,
        (η ((p*n:ℕ)/Y)*Complex.exp (-(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ))))*
          (χ p*((markedMajorLabelMass P:ℂ)*χ n))*markedPrimePhase (p*n) t := by
    apply sum_congr rfl
    intro p hp
    calc
      _ = ∑ n ∈ R,
        (η ((p*n:ℕ)/Y)*Complex.exp (-(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ))))*
          ((markedMajorLabelMass P:ℂ)*χ (p*n))*markedPrimePhase (p*n) t := by
        apply (sum_subset (filter_subset _ _) ?_).symm
        intro n hn hnot
        have hz : η ((p*n:ℕ)/Y)=0 := by
          by_contra hz
          exact hnot (markedMajorCofactorSet_cutoff P η hsupp hY hH (hlo p hp) (hhi p hp) hn hz)
        simp only [hz,zero_mul]
      _ = _ := by
        apply sum_congr rfl
        intro n _
        rw [Nat.cast_mul,map_mul]
        ring
  unfold markedMajorLabelDyad
  rw [hrestrict,markedMajorLabel_finite_mellin η hη ha hsupp S R hS hR
    (fun p => χ p) (fun n => (markedMajorLabelMass P:ℂ)*χ n) θ Y t hY]
  rw [mul_assoc,← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  unfold markedPrimePolynomial markedMajorCofactorPolynomial
  push_cast
  have hHC : (H:ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp
  ring

theorem markedMajorLabelPolynomial_dyad_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P₀ : Finset ℕ) (P : J → Finset ℕ)
    (hP₀ : ∀ p ∈ P₀,p.Prime) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis₀ : ∀ j,Disjoint P₀ (P j)) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (η : ℝ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (θ Y t : ℝ) :
    markedMajorLabelPolynomial (fun j : Option J => j.elim P₀ P) η χ θ Y t =
      ∑ j ∈ markedMajorPrimeDyadIndices P₀,
        markedMajorLabelDyad P (markedMajorPrimeDyad P₀ j) η χ θ Y (bandReciprocalMass P₀) t := by
  classical
  unfold markedMajorLabelPolynomial
  rw [markedMajorLabelSet_option_sum P₀ P hP₀ hP hdis₀ hdis]
  rw [markedMajorPrimeDyad_sum P₀]
  simp only [markedMajorLabelDyad,mul_sum,markedMajorLabelMass_option,Complex.ofReal_mul,
    Complex.ofReal_inv]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro n _
  have he : (((-2*Real.pi*θ*((p*n:ℕ):ℝ)/Y:ℝ):ℂ)*Complex.I) =
      -(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ)) := by push_cast; ring
  rw [he]
  simp only [Nat.cast_mul]
  ring

end ArtinMatthews
