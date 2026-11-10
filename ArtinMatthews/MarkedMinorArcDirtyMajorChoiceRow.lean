module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcDirtyCrudeRow
public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceMass
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual major comparison row, summing all stores, old promotion indices
and true fresh-label measures. The target estimate is derived in the frozen
actual fiber theorem, never supplied as a row-count hypothesis. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyMajorChoiceRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ := by
  classical
  exact ∑ choice : MarkedDirtyFixedEdgeChoice hZ s I,
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1 *
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖

theorem markedDirtyMajorChoiceRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j) {C : ℝ} (hC : 1 ≤ C) (hVC : ∀ j, (V j)⁻¹ ≤ C)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) {c Bτ K H W pmin : ℝ}
    (hY : 1 ≤ Y) (hQ : 0 ≤ Q) (hc : 0 < c) (hBτ : 0 ≤ Bτ) (hpmin : 0 < pmin)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z)=1)
    (hτ : ∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (jstar : I)
    (hp : ∀ k : Fin (s.2.2.1.1 jstar.1:ℕ), pmin ≤ ((s.2.2.2 jstar.1 k).1.1:ℕ)) :
    markedDirtyMajorChoiceRow ν V hZ η ψ r d₀ Y Q ρ w χ s I ≤
      1200*(max 1 (max (Bτ/c) K))^2*C^(Fintype.card J)*H^2*W*(2:ℝ)^(Fintype.card J)*
        (B+1:ℝ)^(Fintype.card J)*
        (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
          finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh)*
        Q^3*(1/pmin+Y^(-1/10:ℝ)) := by
  classical
  let μ := finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
  let A : ℝ := C^(Fintype.card J)*(H^2*(W*(4*Q^3/Y)))*(300*(max 1 (max (Bτ/c) K))^2)*Y*
    (1/pmin+Y^(-1/10:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hμ (fresh) : 0 ≤ μ fresh := Finset.prod_nonneg (fun j _ => hν _ _)
  have hVP : 0 ≤ ∏ j ∈ I, (V j)⁻¹ := Finset.prod_nonneg (fun j _ => (inv_pos.mpr (hV j)).le)
  have hVB : (∏ j ∈ I, (V j)⁻¹) ≤ C^(Fintype.card J) := by
    calc
      _ ≤ ∏ _j ∈ I, C := Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (hV j)).le) (fun j _ => hVC j)
      _ = C^(I.card) := by simp
      _ ≤ _ := pow_le_pow_right₀ hC (Finset.card_le_card (Finset.subset_univ I))
  have hpoint (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
      (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1)) :
      (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
        markedRawEdgeChoicePrimeMass ν V hZ s choice.1 *
          ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
            (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖) ≤ A*μ fresh := by
    have hf := markedDirtyMajorChoiceFiber_sum_norm_le hZ η ψ r d₀ Y Q ρ hY hQ hc hBτ hρ₀ hρ₁ hH hW
      hη hψ hsupp w hw hτ χ hχ s I store indices fresh jstar
    have hrec : 1/((s.2.2.2 jstar.1 (indices jstar)).1.1:ℕ) ≤ 1/pmin :=
      one_div_le_one_div_of_le hpmin (hp (indices jstar))
    have hn := hf.trans (mul_le_mul_of_nonneg_left (add_le_add hrec le_rfl)
      (by positivity : 0 ≤ (H^2*(W*(4*Q^3/Y)))*(300*(max 1 (max (Bτ/c) K))^2)*Y))
    calc
      _ = (μ fresh*(∏ j ∈ I, (V j)⁻¹))*
          ∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
            ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
              (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro choice hchoice
        rw [markedDirtyMajorChoiceFiber_prime_mass ν V hZ s I store indices fresh choice hchoice]
      _ ≤ (μ fresh*C^(Fintype.card J))*
          ((H^2*(W*(4*Q^3/Y)))*(300*(max 1 (max (Bτ/c) K))^2)*Y*(1/pmin+Y^(-1/10:ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVB (hμ fresh)) hn
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (mul_nonneg (hμ fresh) (pow_nonneg (by linarith) _))
      _ = _ := by dsimp [A]; ring
  have hidx : (Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ) ≤ (B+1:ℝ)^(Fintype.card J) := by
    have hh : Fintype.card (MarkedRawPromotionTuple s.2.2 I) ≤ (B+1)^(Fintype.card J) :=
      (markedRawPromotionTuple_card_le s.2.2 I).trans ((Nat.pow_le_pow_left (by omega : B ≤ B+1) _).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ B+1) (Finset.card_le_card (Finset.subset_univ I))))
    exact_mod_cast hh
  unfold markedDirtyMajorChoiceRow
  rw [markedDirtyMajorChoice_fiberwise_sum hZ s I]
  calc
    _ ≤ ∑ _store : J → Bool, ∑ _indices : MarkedRawPromotionTuple s.2.2 I,
        ∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1), A*μ fresh :=
      Finset.sum_le_sum (fun store _ => Finset.sum_le_sum (fun indices _ =>
        Finset.sum_le_sum (fun fresh _ => hpoint store indices fresh)))
    _ = (2:ℝ)^(Fintype.card J)*(Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ)*
        (A*∑ fresh, μ fresh) := by simp [Finset.mul_sum,mul_assoc]
    _ ≤ (2:ℝ)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*(A*∑ fresh, μ fresh) := by
      gcongr
      exact mul_nonneg hA (Finset.sum_nonneg (fun fresh _ => hμ fresh))
    _ = _ := by
      dsimp [A,μ]
      field_simp [show Y≠0 by linarith]
      ring

end ArtinMatthews
