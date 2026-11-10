module

public import ArtinMatthews.MarkedMajorArcPrimeNormalization
public import ArtinMatthews.MarkedSparsePhaseKernel
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import ArtinMatthews.SourceComparisonPolynomialMean
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.JointDickman.Amplification.RamanujanRoots


set_option backward.privateInPublic true
@[expose] public section

/-! Exact separation of the rational additive phase in the positive tuple
and constant branches. The cofactor is allowed to lie in a nonunit class. -/

namespace ArtinMatthews

open Finset

noncomputable section

def sourceComparisonResidueFiber {q : ℕ} (S : Finset ℕ) (r : ZMod q) : Finset ℕ :=
  S.filter (fun n => (n:ZMod q)=r)

theorem sourceComparison_sum_residue_fibers {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (f : ℕ → A) :
    (∑ n ∈ S, f n) = ∑ r : ZMod q, ∑ n ∈ sourceComparisonResidueFiber S r, f n := by
  have hm : ∀ n ∈ S, (n:ZMod q) ∈ (univ : Finset (ZMod q)) := fun n _ => mem_univ _
  exact (sum_fiberwise_of_maps_to hm f).symm

theorem sourceComparisonPrimePolynomial_trivial (S : Finset ℕ) (P t : ℝ) :
    markedPrimePolynomial S P (1 : DirichletCharacter ℂ 1) 0 t =
      (∑ p ∈ S, markedPrimePhase p t)/P := by
  unfold markedPrimePolynomial
  simp only [add_zero]
  congr 1
  apply sum_congr rfl
  intro p _
  rw [Subsingleton.elim (p:ZMod 1) 1, map_one, one_mul]

/-- The rational phase in the paper is the actual finite additive character. -/
theorem sourceComparisonAdditivePhase_eq {q : ℕ} [NeZero q] (h n : ℕ) :
    ZMod.stdAddChar ((h:ZMod q)*(n:ZMod q)) =
      Complex.exp (((2*Real.pi*((h:ℝ)*(n:ℝ)/(q:ℝ)):ℝ):ℂ)*Complex.I) := by
  rw [← Nat.cast_mul, OAI.JointDickman.stdAddChar_natCast]
  congr 1
  push_cast
  ring

def sourceComparisonUnitFourierCoefficient {q : ℕ} [NeZero q] (w : ZMod q → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient:ℂ)⁻¹ * ∑ r : (ZMod q)ˣ, w r * χ ((r:ZMod q)⁻¹)

theorem sourceComparisonUnitFourierCoefficient_norm_le {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1) (χ : DirichletCharacter ℂ q) :
    ‖sourceComparisonUnitFourierCoefficient w χ‖ ≤ 1 := by
  have hq : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  unfold sourceComparisonUnitFourierCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient:ℝ)⁻¹ * ∑ r : (ZMod q)ˣ, ‖w r*χ ((r:ZMod q)⁻¹)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq.le)
    _ ≤ (q.totient:ℝ)⁻¹ * ∑ _r : (ZMod q)ˣ, (1:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      apply sum_le_sum
      intro r _
      rw [norm_mul]
      exact (mul_le_mul (hw r) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = 1 := by simp [ZMod.card_units_eq_totient, hq.ne']

theorem sourceComparisonUnitFourier_expand {q : ℕ} [NeZero q] (w : ZMod q → ℂ)
    (z : ZMod q) (hz : IsUnit z) :
    w z = ∑ χ : DirichletCharacter ℂ q, sourceComparisonUnitFourierCoefficient w χ * χ z := by
  classical
  obtain ⟨u, rfl⟩ := hz
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  symm
  calc
    _ = (q.totient:ℂ)⁻¹ * ∑ r : (ZMod q)ˣ,
        w r * ∑ χ : DirichletCharacter ℂ q, χ ((r:ZMod q)⁻¹)*χ u := by
      unfold sourceComparisonUnitFourierCoefficient
      simp only [mul_assoc, sum_mul]
      rw [← mul_sum, sum_comm]
      apply congrArg ((q.totient:ℂ)⁻¹ * ·)
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
    _ = (q.totient:ℂ)⁻¹ * ∑ r : (ZMod q)ˣ, w r *
        (if (r:ZMod q) = (u:ZMod q) then (q.totient:ℂ) else 0) := by
      apply congrArg ((q.totient:ℂ)⁻¹ * ·)
      apply sum_congr rfl
      intro r _
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit (u:ZMod q)]
    _ = _ := by
      rw [sum_eq_single u]
      · simp [hφ, mul_left_comm]
      · intro r _ hru
        simp [show (r:ZMod q) ≠ (u:ZMod q) from fun he => hru (Units.ext he)]
      · simp

theorem sourceComparisonDirichletCharacter_card_le (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) ≤ q := by
  rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  exact Nat.totient_le _

def sourceComparisonConstantBox {q : ℕ} [NeZero q]
    (h : ZMod q) (S R : Finset ℕ) (a : ℕ → ℂ) (P U t : ℝ) : ℂ :=
  (∑ p ∈ S, ∑ n ∈ R, a n*ZMod.stdAddChar (h*((p*n:ℕ):ZMod q))*
    markedPrimePhase (p*n) t) / (P*U:ℝ)

def sourceComparisonTupleBox {q : ℕ} [NeZero q]
    (h : ZMod q) (S L R : Finset ℕ) (a : ℕ → ℂ) (P H U t : ℝ) : ℂ :=
  (∑ p ∈ S, ∑ m ∈ L, ∑ n ∈ R, a n*ZMod.stdAddChar (h*((p*m*n:ℕ):ZMod q))*
    markedPrimePhase (p*m*n) t) / (P*H*U:ℝ)

theorem sourceComparisonConstantBox_factor {q : ℕ} [NeZero q]
    (h : ZMod q) (S : Finset ℕ) (l r : ℕ) (a : ℕ → ℂ) (P U t : ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hl : 0 < l) :
    sourceComparisonConstantBox h S (Icc l r) a P U t =
      ∑ v : ZMod q, markedPrimePolynomial (sourceComparisonResidueFiber S v) P
        (1 : DirichletCharacter ℂ 1) 0 t *
        markedDyadicPolynomial l r U (fun n => a n*ZMod.stdAddChar (h*v*(n:ZMod q))) t := by
  have hf (v : ZMod q) :
      (∑ p ∈ sourceComparisonResidueFiber S v, ∑ n ∈ Icc l r,
        a n*ZMod.stdAddChar (h*((p*n:ℕ):ZMod q))*markedPrimePhase (p*n) t) =
      (∑ p ∈ sourceComparisonResidueFiber S v, markedPrimePhase p t) *
        ∑ n ∈ Icc l r, (a n*ZMod.stdAddChar (h*v*(n:ZMod q)))*markedPrimePhase n t := by
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hp' := mem_filter.mp hp
    rw [Nat.cast_mul, ← mul_assoc h, hp'.2,
      ← markedPrimePhase_mul (hS p hp'.1) (hl.trans_le (mem_Icc.mp hn).1)]
    ring
  rw [sourceComparisonConstantBox, sourceComparison_sum_residue_fibers (q := q)]
  rw [sum_div]
  apply sum_congr rfl
  intro v _
  rw [hf, sourceComparisonPrimePolynomial_trivial, markedDyadicPolynomial, Complex.ofReal_mul]
  ring

/-- Exact unit-character expansion for the giant prime after splitting the
small prime and the cofactor into their finite residue classes. -/
theorem sourceComparisonTupleBox_factor {q : ℕ} [NeZero q]
    (h : ZMod q) (S : Finset ℕ) (l r : ℕ) (a : ℕ → ℂ) (P H U u v t : ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hl : 0 < l)
    (hunit : ∀ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, IsUnit (m:ZMod q)) :
    sourceComparisonTupleBox h S ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime) (Icc l r)
      a P H U t =
      ∑ v₁ : ZMod q, ∑ v₂ : ZMod q, ∑ χ : DirichletCharacter ℂ q,
        sourceComparisonUnitFourierCoefficient (fun z => ZMod.stdAddChar (h*v₁*z*v₂)) χ *
          (markedPrimePolynomial (sourceComparisonResidueFiber S v₁) P
            (1 : DirichletCharacter ℂ 1) 0 t * markedMajorNormalizedPrimeSum χ t H u v *
          markedDyadicPolynomial l r U (fun n => if (n:ZMod q)=v₂ then a n else 0) t) := by
  classical
  let L := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  let R := Icc l r
  let w (v₁ v₂ : ZMod q) (z : ZMod q) := ZMod.stdAddChar (h*v₁*z*v₂)
  let C (v₁ v₂ : ZMod q) (χ : DirichletCharacter ℂ q) :=
    sourceComparisonUnitFourierCoefficient (w v₁ v₂) χ
  let b (p m n : ℕ) := a n*ZMod.stdAddChar (h*((p*m*n:ℕ):ZMod q))*markedPrimePhase (p*m*n) t
  have hswap : (∑ p ∈ S, ∑ m ∈ L, ∑ n ∈ R, b p m n) =
      ∑ p ∈ S, ∑ n ∈ R, ∑ m ∈ L, b p m n := by
    apply sum_congr rfl
    intro p _
    rw [sum_comm]
  have hsplit : (∑ p ∈ S, ∑ n ∈ R, ∑ m ∈ L, b p m n) =
      ∑ v₁ : ZMod q, ∑ v₂ : ZMod q, ∑ p ∈ sourceComparisonResidueFiber S v₁,
        ∑ n ∈ sourceComparisonResidueFiber R v₂, ∑ m ∈ L, b p m n := by
    rw [sourceComparison_sum_residue_fibers (q := q) S]
    apply sum_congr rfl
    intro v₁ _
    simp_rw [sourceComparison_sum_residue_fibers (q := q) R]
    rw [sum_comm]
  have hexpand (v₁ v₂ : ZMod q) :
      (∑ p ∈ sourceComparisonResidueFiber S v₁, ∑ n ∈ sourceComparisonResidueFiber R v₂,
        ∑ m ∈ L, b p m n) =
      ∑ χ : DirichletCharacter ℂ q, C v₁ v₂ χ *
        ((∑ p ∈ sourceComparisonResidueFiber S v₁, markedPrimePhase p t) *
        (∑ m ∈ L, χ (m:ZMod q)*markedPrimePhase m t) *
        ∑ n ∈ sourceComparisonResidueFiber R v₂, a n*markedPrimePhase n t) := by
    have hterm (p n m : ℕ) (hp : p ∈ sourceComparisonResidueFiber S v₁)
        (hn : n ∈ sourceComparisonResidueFiber R v₂) (hm : m ∈ L) :
        b p m n = ∑ χ : DirichletCharacter ℂ q, C v₁ v₂ χ *
          (markedPrimePhase p t*(χ (m:ZMod q)*markedPrimePhase m t)*(a n*markedPrimePhase n t)) := by
      have hp' := mem_filter.mp hp
      have hn' := mem_filter.mp hn
      have hm0 : 0 < m := (mem_filter.mp hm).2.pos
      have hp0 := hS p hp'.1
      have hn0 := hl.trans_le (mem_Icc.mp hn'.1).1
      dsimp [b]
      rw [Nat.cast_mul, Nat.cast_mul, hp'.2, hn'.2,
        ← markedPrimePhase_mul (Nat.mul_pos hp0 hm0) hn0, ← markedPrimePhase_mul hp0 hm0]
      rw [show h*(v₁*(m:ZMod q)*v₂) = h*v₁*(m:ZMod q)*v₂ by ring]
      change a n*w v₁ v₂ (m:ZMod q)*(markedPrimePhase p t*markedPrimePhase m t*markedPrimePhase n t) = _
      rw [sourceComparisonUnitFourier_expand (w v₁ v₂) (m:ZMod q) (hunit m hm)]
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro χ _
      dsimp [C]
      ring
    calc
      _ = ∑ p ∈ sourceComparisonResidueFiber S v₁,
          ∑ n ∈ sourceComparisonResidueFiber R v₂, ∑ m ∈ L,
          ∑ χ : DirichletCharacter ℂ q, C v₁ v₂ χ *
            (markedPrimePhase p t*(χ (m:ZMod q)*markedPrimePhase m t)*(a n*markedPrimePhase n t)) := by
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro n hn
        exact sum_congr rfl (fun m hm => hterm p n m hp hn hm)
      _ = _ := by
        simp_rw [sum_comm (s := L) (t := (univ : Finset (DirichletCharacter ℂ q)))]
        simp_rw [sum_comm (s := sourceComparisonResidueFiber R v₂)
          (t := (univ : Finset (DirichletCharacter ℂ q)))]
        rw [sum_comm]
        apply sum_congr rfl
        intro χ _
        let D := C v₁ v₂ χ
        let F (p : ℕ) := markedPrimePhase p t
        let G (m : ℕ) := χ (m:ZMod q)*markedPrimePhase m t
        let V (n : ℕ) := a n*markedPrimePhase n t
        let P₁ := sourceComparisonResidueFiber S v₁
        let P₂ := sourceComparisonResidueFiber R v₂
        change (∑ p ∈ P₁, ∑ n ∈ P₂, ∑ m ∈ L, D*(F p*G m*V n)) =
          D*((∑ p ∈ P₁, F p)*(∑ m ∈ L, G m)*(∑ n ∈ P₂, V n))
        calc
          _ = ∑ p ∈ P₁, ∑ n ∈ P₂, (∑ m ∈ L, G m)*(D*F p*V n) := by
            apply sum_congr rfl
            intro p _
            apply sum_congr rfl
            intro n _
            rw [sum_mul]
            apply sum_congr rfl
            intro m _
            ring
          _ = ∑ p ∈ P₁, ((∑ m ∈ L, G m)*(∑ n ∈ P₂, V n))*(D*F p) := by
            apply sum_congr rfl
            intro p _
            rw [mul_sum, sum_mul]
            apply sum_congr rfl
            intro n _
            ring
          _ = _ := by
            rw [← mul_sum, ← mul_sum]
            ring
  change (∑ p ∈ S, ∑ m ∈ L, ∑ n ∈ R, b p m n) / ((P*H*U:ℝ):ℂ) = _
  rw [hswap, hsplit]
  simp_rw [hexpand, sum_div]
  apply sum_congr rfl
  intro v₁ _
  apply sum_congr rfl
  intro v₂ _
  apply sum_congr rfl
  intro χ _
  rw [sourceComparisonPrimePolynomial_trivial, markedMajorNormalizedPrimeSum,
    markedDyadicPolynomial]
  have he : (∑ m ∈ L, χ (m:ZMod q)*(m:ℂ)^((t:ℂ)*Complex.I)) =
      ∑ m ∈ L, χ (m:ZMod q)*markedPrimePhase m t := by
    apply sum_congr rfl
    intro m hm
    rw [sourceComparisonPrimePhase_eq_cpow (mem_filter.mp hm).2.pos]
  have hRsum : (∑ n ∈ R, (if (n:ZMod q)=v₂ then a n else 0)*markedPrimePhase n t) =
      ∑ n ∈ sourceComparisonResidueFiber R v₂, a n*markedPrimePhase n t := by
    rw [sourceComparisonResidueFiber, sum_filter]
    apply sum_congr rfl
    intro n _
    split_ifs <;> simp
  rw [he, hRsum]
  simp only [C, w, Complex.ofReal_mul]
  ring

end
end ArtinMatthews
