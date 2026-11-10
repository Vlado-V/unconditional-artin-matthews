module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMinorArcDirtyCrudeRow
public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceMass
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeFiber
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual stores, indexed promotions and fresh prime integrations in the
full signed edge row. The bound has no source-slot cardinality loss. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedRawEdgeCrudeFixedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ :=
  ∑ choice : MarkedDirtyFixedEdgeChoice hZ s I,
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖

def markedRawEdgeCrudeAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ choice : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoicePrimeMass ν V hZ s choice*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖

theorem markedRawEdgeCrudeAbsRow_partition {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeCrudeAbsRow ν V hZ ψ η d₀ Y Q ρ χ s =
      ∑ I : Finset J,markedRawEdgeCrudeFixedAbsRow ν V hZ ψ η d₀ Y Q ρ χ s I := by
  classical
  have hh := Equiv.sum_comp (Equiv.sigmaFiberEquiv (fun c : MarkedRawEdgeChoice hZ s =>
    markedDirtyEdgePromotedGroups c.promotions))
    (fun c => markedRawEdgeChoicePrimeMass ν V hZ s c*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖)
  simpa only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply,markedRawEdgeCrudeAbsRow,
    markedRawEdgeCrudeFixedAbsRow] using hh.symm

theorem markedRawEdgeCrude_fresh_mass_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {N : ℝ} (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N) (I : Finset J) :
    (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
      finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh) ≤ N^(Fintype.card J) := by
  classical
  calc
    _ = ∏ j : ↥(Finset.univ \ I),∑ p,ν j.1 p := (Fintype.prod_sum _).symm
    _ ≤ ∏ _j : ↥(Finset.univ \ I),N := Finset.prod_le_prod₀
      (fun j _ => Finset.sum_nonneg (fun p _ => hν j.1 p)) (fun j _ => hνN j.1)
    _ = N^(Fintype.card ↥(Finset.univ \ I)) := by
      simp only [Finset.prod_const,Finset.card_univ]
    _ ≤ _ := pow_le_pow_right₀ hN (by simpa only [Fintype.card_coe,Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ (Finset.univ \ I))))

theorem markedRawEdgeCrude_fixed_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A : ℝ)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) (I : Finset J) :
    markedRawEdgeCrudeFixedAbsRow ν V hZ ψ η d₀ Y Q ρ χ s I ≤
      (2*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  classical
  let E := H^2*(33*W*(1+(2*A*Y+1)*(4*Q^3/Y)))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let μ := finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
  have hμ (fresh) : 0 ≤ μ fresh := Finset.prod_nonneg (fun j _ => hν _ _)
  have hVP : 0 ≤ ∏ j ∈ I,(V j)⁻¹ := Finset.prod_nonneg (fun j _ => (inv_pos.mpr (hV j)).le)
  have hVB : (∏ j ∈ I,(V j)⁻¹) ≤ C^(Fintype.card J) := by
    calc
      _ ≤ ∏ _j ∈ I,C := Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (hV j)).le) (fun j _ => hVC j)
      _ = C^I.card := by simp
      _ ≤ _ := pow_le_pow_right₀ hC (Finset.card_le_card (Finset.subset_univ I))
  have hpoint (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
      (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1)) :
      (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
        markedRawEdgeChoicePrimeMass ν V hZ s choice.1*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖) ≤
        C^(Fintype.card J)*E*μ fresh := by
    have hf := markedRawEdgeCrude_fiber_sum_le hZ ψ η r d₀ Y Q ρ H W A hY hQ hA hρ₀ hρ₁ hH hW
      hη hψ hsupp χ hχ s w hw hτ hbox I store indices fresh
    calc
      _ = (μ fresh*(∏ j ∈ I,(V j)⁻¹))*∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun choice hc => by
          rw [markedDirtyMajorChoiceFiber_prime_mass ν V hZ s I store indices fresh choice hc])
      _ ≤ (μ fresh*C^(Fintype.card J))*E := mul_le_mul
        (mul_le_mul_of_nonneg_left hVB (hμ fresh)) hf
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (mul_nonneg (hμ fresh) (pow_nonneg (by linarith) _))
      _ = _ := by ring
  have hidx : (Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ) ≤ (B+1:ℝ)^(Fintype.card J) := by
    have hh : Fintype.card (MarkedRawPromotionTuple s.2.2 I) ≤ (B+1)^(Fintype.card J) :=
      (markedRawPromotionTuple_card_le s.2.2 I).trans ((Nat.pow_le_pow_left (by omega : B ≤ B+1) _).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ B+1) (Finset.card_le_card (Finset.subset_univ I))))
    exact_mod_cast hh
  have hm := markedRawEdgeCrude_fresh_mass_le ν hν hN hνN I
  have hsum : 0 ≤ ∑ fresh,μ fresh := Finset.sum_nonneg (fun fresh _ => hμ fresh)
  unfold markedRawEdgeCrudeFixedAbsRow
  rw [markedDirtyMajorChoice_fiberwise_sum hZ s I]
  calc
    _ ≤ ∑ _store : J → Bool,∑ _indices : MarkedRawPromotionTuple s.2.2 I,
        ∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),C^(Fintype.card J)*E*μ fresh :=
      Finset.sum_le_sum (fun store _ => Finset.sum_le_sum (fun indices _ =>
        Finset.sum_le_sum (fun fresh _ => hpoint store indices fresh)))
    _ = (2:ℝ)^(Fintype.card J)*(Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ)*
        (C^(Fintype.card J)*E*(∑ fresh,μ fresh)) := by simp [Finset.mul_sum,mul_assoc]
    _ ≤ (2:ℝ)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*
        (C^(Fintype.card J)*E*N^(Fintype.card J)) := by
      gcongr
    _ = _ := by dsimp [E]; simp only [mul_pow]; ring

/-- All Boolean stores, all actual indexed promotions, every fresh draw,
and every literal target are included. The source-slot count does not enter. -/
theorem markedRawEdgeCrude_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A : ℝ)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) :
    markedRawEdgeCrudeAbsRow ν V hZ ψ η d₀ Y Q ρ χ s ≤
      (4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  classical
  rw [markedRawEdgeCrudeAbsRow_partition]
  calc
    _ ≤ ∑ _I : Finset J,
        (2*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
          (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) :=
      Finset.sum_le_sum (fun I _ => markedRawEdgeCrude_fixed_row_le ν V hν hV hC hVC hN hνN
        hZ ψ η r d₀ Y Q ρ H W A hY hQ hA hρ₀ hρ₁ hH hW hη hψ hsupp χ hχ s w hw hτ hbox I)
    _ = _ := by
      simp only [Finset.sum_const,Fintype.card_finset,Finset.card_univ,
        nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      simp only [mul_pow]
      rw [show (4:ℝ)^(Fintype.card J)=(2:ℝ)^(Fintype.card J)*(2:ℝ)^(Fintype.card J) by
        rw [← mul_pow]; norm_num]
      ring

theorem markedRawEdgeCrude_kernel_factor_le_polynomial {Y Q A W : ℝ}
    (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hW : 0 ≤ W) :
    33*W*(1+(2*A*Y+1)*(4*Q^3/Y)) ≤ (33*W*(8*A+5))*Q^3 := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hq3 : 1 ≤ Q^3 := one_le_pow₀ hQ
  have hi : 1/Y ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hY
  calc
    _ = 33*W*(1+(8*A+4*(1/Y))*Q^3) := by field_simp [hYpos.ne']; ring
    _ ≤ 33*W*(Q^3+(8*A+4)*Q^3) :=
      mul_le_mul_of_nonneg_left (add_le_add hq3
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (by positivity)
    _ = _ := by ring

end ArtinMatthews
