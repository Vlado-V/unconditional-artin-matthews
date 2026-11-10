module

public import ArtinMatthews.SourceComparisonResidueFactorization
public import ArtinMatthews.SourceComparisonHighTimeTuple
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.GiantCharacterGraph
public import ArtinMatthews.MarkedMajorArcExceptionalCover
public import ArtinMatthews.MarkedSparsePhaseContinuity
public import ArtinMatthews.SourceComparisonPolynomialMean
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! High-time energy of the literal finite dyads with their additive phase. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

theorem sourceComparison_finiteSum_energy {ι : Type*} (J : Finset ι)
    (f : ι → ℝ → ℂ) {T : ℝ} {W : Set ℝ} (hW : W ⊆ Set.Icc (-T) T)
    (hf : ∀ j ∈ J, Continuous (f j)) {E : ℝ}
    (he : ∀ j ∈ J, (∫ t in W, ‖f j t‖^2) ≤ E) :
    (∫ t in W, ‖∑ j ∈ J, f j t‖^2) ≤ (J.card:ℝ)^2*E := by
  have hi : ∀ j ∈ J, IntegrableOn (fun t => ‖f j t‖^2) W := fun j hj =>
    ((hf j hj).norm.pow 2).integrableOn_Icc.mono_set hW
  have hc : Continuous (fun t => ∑ j ∈ J,f j t) := continuous_finsetSum J hf
  calc
    _ ≤ ∫ t in W, (J.card:ℝ)*∑ j ∈ J, ‖f j t‖^2 := by
      apply integral_mono ((hc.norm.pow 2).integrableOn_Icc.mono_set hW)
        ((integrable_finsetSum J hi).const_mul _)
      intro t
      change ‖∑ j ∈ J,f j t‖^2 ≤ _
      have hcs := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun j => ‖f j t‖)
      simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs
    _ = (J.card:ℝ)*∑ j ∈ J, (∫ t in W, ‖f j t‖^2) := by
      rw [integral_const_mul, integral_finsetSum J hi]
    _ ≤ (J.card:ℝ)*∑ _j ∈ J, E := mul_le_mul_of_nonneg_left (sum_le_sum he) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

theorem sourceComparisonTupleBox_high_energy
    (c C σ d a η τ D A : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hσ : 0 ≤ σ) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
        1 < P → c*X^(1/(10:ℝ)) ≤ Real.log P → Real.log P ≤ C*X →
        1 < T → T ≤ Real.exp (2*X) →
        Real.exp (τ*X) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*X) →
        Real.exp (d*X) ≤ U → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        T ≤ H*U → H*U ≤ Real.exp (σ*X) → (∀ n ∈ Finset.Icc l r, ‖β n‖ ≤ X^D) →
        ∀ (q : ℕ) [NeZero q] (h : ZMod q), (q:ℝ) ≤ X^a →
          (∀ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, IsUnit (m:ZMod q)) →
          ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*P) →
          (∫ t in sourceComparisonHighTimes T (X^B),
            ‖sourceComparisonTupleBox h S ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime)
              (Icc l r) β P H U t‖^2) ≤ X^(-A) := by
  let R := A+6*a
  obtain ⟨B,hB,hbox⟩ := sourceComparisonHighTime_tuple c C σ d a η τ D R
    hc hC hσ hd ha hη hτ hD (by dsimp [R]; positivity)
  refine ⟨B,hB,?_⟩
  filter_upwards [hbox, eventually_ge_atTop (1:ℝ)] with X hbox hX
  have hX0 : 0 < X := by linarith
  intro P T H u v U l r β hP hlo hhi hT hTU hH hHu huv hvH hvhi hU hl hr hTH hHcap hβ
    q _ h hq hunit S hS hScap
  let W := sourceComparisonHighTimes T (X^B)
  have hW : W ⊆ Set.Icc (-T) T := fun _ ht => ht.1
  have hl0 : 0 < l := by exact_mod_cast (Real.exp_pos _).trans_le (hU.trans hl)
  let f (v₁ v₂ : ZMod q) (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    sourceComparisonUnitFourierCoefficient (fun z => ZMod.stdAddChar (h*v₁*z*v₂)) χ *
      (markedPrimePolynomial (sourceComparisonResidueFiber S v₁) P (1:DirichletCharacter ℂ 1) 0 t *
        markedMajorNormalizedPrimeSum χ t H u v *
        markedDyadicPolynomial l r U (fun n => if (n:ZMod q)=v₂ then β n else 0) t)
  have hf (v₁ v₂ : ZMod q) (χ : DirichletCharacter ℂ q) : Continuous (f v₁ v₂ χ) := by
    exact continuous_const.mul (((markedPrimePolynomial_continuous _ _ _ _).mul
      (sourceComparisonNormalizedPrime_continuous _ _ _ _)).mul
        (markedDyadicPolynomial_continuous _ _ _ _))
  have hsingle (v₁ v₂ : ZMod q) (χ : DirichletCharacter ℂ q) :
      (∫ t in W, ‖f v₁ v₂ χ t‖^2) ≤ X^(-R) := by
    let S₁ := sourceComparisonResidueFiber S v₁
    let β₂ : ℕ → ℂ := fun n => if (n:ZMod q)=v₂ then β n else 0
    have hβ₂ (n : ℕ) (hn : n ∈ Icc l r) : ‖β₂ n‖ ≤ X^D := by
      dsimp [β₂]
      split_ifs
      · exact hβ n hn
      · simp only [norm_zero]
        positivity
    have hb := hbox P T H u v U l r β₂ hP hlo hhi hT hTU hH hHu huv hvH hvhi
      hU hl hr hTH hHcap hβ₂ q χ hq 1 1 0 S₁
      (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => hScap p (mem_filter.mp hp).1)
    have hC := sourceComparisonUnitFourierCoefficient_norm_le
      (fun z => ZMod.stdAddChar (h*v₁*z*v₂)) (fun z => (giant_stdAddChar_norm _).le) χ
    simp only [f, norm_mul, mul_pow]
    simp only [norm_mul, mul_pow] at hb
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans
      (by
        have hCs := pow_le_pow_left₀ (norm_nonneg _) hC 2
        simpa only [one_pow, one_mul] using
          mul_le_mul_of_nonneg_right hCs (Real.rpow_nonneg hX0.le (-R)))
  have hinner (v₁ v₂ : ZMod q) :
      (∫ t in W, ‖∑ χ : DirichletCharacter ℂ q, f v₁ v₂ χ t‖^2) ≤ (q:ℝ)^2*X^(-R) := by
    apply (sourceComparison_finiteSum_energy univ (f v₁ v₂) hW
      (fun χ _ => hf v₁ v₂ χ) (fun χ _ => hsingle v₁ v₂ χ)).trans
    have hcard : ((univ : Finset (DirichletCharacter ℂ q)).card:ℝ) ≤ q := by
      simpa only [card_univ] using (show (Fintype.card (DirichletCharacter ℂ q):ℝ) ≤ q by
        exact_mod_cast sourceComparisonDirichletCharacter_card_le q)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard 2) (by positivity)
  have hmiddle (v₁ : ZMod q) :
      (∫ t in W, ‖∑ v₂ : ZMod q, ∑ χ : DirichletCharacter ℂ q, f v₁ v₂ χ t‖^2) ≤
        (q:ℝ)^2*((q:ℝ)^2*X^(-R)) := by
    simpa only [card_univ, ZMod.card] using
      sourceComparison_finiteSum_energy (univ : Finset (ZMod q))
        (fun v₂ t => ∑ χ : DirichletCharacter ℂ q, f v₁ v₂ χ t) hW
        (fun v₂ _ => continuous_finsetSum _ (fun χ _ => hf v₁ v₂ χ))
        (fun v₂ _ => hinner v₁ v₂)
  have houter := sourceComparison_finiteSum_energy (univ : Finset (ZMod q))
    (fun v₁ t => ∑ v₂ : ZMod q, ∑ χ : DirichletCharacter ℂ q, f v₁ v₂ χ t) hW
    (fun v₁ _ => continuous_finsetSum _ (fun v₂ _ => continuous_finsetSum _ (fun χ _ => hf v₁ v₂ χ)))
    (fun v₁ _ => hmiddle v₁)
  simp only [card_univ, ZMod.card] at houter
  simp_rw [sourceComparisonTupleBox_factor h S l r β P H U u v _
    (fun p hp => (hS p hp).pos) hl0 hunit]
  change (∫ t in W, ‖∑ v₁ : ZMod q, ∑ v₂ : ZMod q,
    ∑ χ : DirichletCharacter ℂ q, f v₁ v₂ χ t‖^2) ≤ _
  apply houter.trans
  calc
    _ = (q:ℝ)^6*X^(-R) := by ring
    _ ≤ (X^a)^6*X^(-R) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 6) (by positivity)
    _ = X^(-A) := by
      rw [← Real.rpow_mul_natCast hX0.le, ← Real.rpow_add hX0]
      congr 1
      dsimp [R]
      push_cast
      ring

end
end ArtinMatthews
