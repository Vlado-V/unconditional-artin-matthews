module

public import ArtinMatthews.IdealCharacterDyadComparison
public import ArtinMatthews.IdealDyadicEnergy
public import ArtinMatthews.IdealDyadicOrigin
public import ArtinMatthews.IdealGroupedSlotCount
public import ArtinMatthews.IdealProductDyadicBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual harmonic character/log-cell kernel compares the full
unmasked product phase uniformly at every real additive frequency. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def idealComparisonPrecision (d A₀ : ℝ) : ℝ := A₀+2*d+7

theorem idealCharacterCell_comparison (m : ℕ) (C₀ v₀ c d C A₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d)
    (hC : 0 ≤ C) (hA₀ : 0 ≤ A₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ),
      (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
      Pairwise (fun i j => Disjoint (P i) (P j)) → Pairwise (fun i j => Disjoint (R i) (R j)) →
      (∀ i, v₀ ≤ bandReciprocalMass (P i)) → (∀ i, v₀ ≤ bandReciprocalMass (R i)) →
      (∀ i, k i ≤ m) → (∀ i, l i ≤ m) →
      (Fintype.card A : ℝ) ≤ C₀*Real.log L → (Fintype.card B : ℝ) ≤ C₀*Real.log L →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (∀ i p, p ∈ R i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      ∀ (i : Σ a, Fin (k a)) (j : Σ b, Fin (l b)), IdealPrimeInterval (P i.1) → IdealPrimeInterval (R j.1) →
      ∀ (ζ α : ℝ), |ζ| ≤ L^C →
      ∀ (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
        (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ),
      ‖∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
        ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
          (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
            idealFullCellPhaseAverage (fun z : Σ i, Fin (k i) => P z.1)
              (fun z : Σ i, Fin (l i) => R z.1)
              ⌊L^(idealMinorBilinearExponent m C₀ v₀ d (idealComparisonPrecision d A₀))⌋₊
              (L^(-idealComparisonWidth m C₀ v₀ d C (idealComparisonPrecision d A₀)))
              (L^(-idealComparisonThreshold m C₀ v₀ d C (idealComparisonPrecision d A₀))) ζ α x y)‖ ≤
        L^(-A₀)*Real.sqrt (idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f)*
          Real.sqrt (idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g) := by
  let E := idealComparisonPrecision d A₀
  have hE : 0 ≤ E := by dsimp [E, idealComparisonPrecision]; linarith
  filter_upwards [idealCharacterDyad_comparison.{u,v} m C₀ v₀ c d C E hC₀ hv₀ hc hd hC hE,
    idealSelectedProductDyadicOrigin_uniform.{u} c d ((m : ℝ)*C₀),
    idealSelectedProductDyadicOrigin_uniform.{v} c d ((m : ℝ)*C₀),
    idealSelectedProductDyads_uniform.{u} d ((m : ℝ)*C₀) hd,
    idealSelectedProductDyads_uniform.{v} d ((m : ℝ)*C₀) hd,
    eventually_ge_atTop (2 : ℝ)] with L hdyad horiginP horiginR hcountP hcountR hL2
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  intro A B _ _ _ _ P k R l hP hR hdisP hdisR hVP hVR hk hl hcardP hcardR hbP hbR i j hi hj
    ζ α hζ f g
  let P' := fun z : Σ a, Fin (k a) => P z.1
  let R' := fun z : Σ b, Fin (l b) => R z.1
  let p := idealSelectedProduct (P := P')
  let q := idealSelectedProduct (P := R')
  let μ := idealSelectedMass P'
  let ν := idealSelectedMass R'
  let Q := ⌊L^(idealMinorBilinearExponent m C₀ v₀ d E)⌋₊
  let H := idealComparisonWidth m C₀ v₀ d C E
  let X := idealComparisonThreshold m C₀ v₀ d C E
  let K := fun x : IdealSelectedLabels P' => fun y : IdealSelectedLabels R' =>
    idealProductPhase ζ α (p x) (q y)-idealFullCellPhaseAverage P' R' Q (L^(-H)) (L^(-X)) ζ α x y
  have hpP : ∀ z p, p ∈ P' z → p.Prime := fun z p hp => hP z.1 p hp
  have hpR : ∀ z p, p ∈ R' z → p.Prime := fun z p hp => hR z.1 p hp
  have hboundsP := fun (z : Σ a, Fin (k a)) => hbP z.1
  have hboundsR := fun (z : Σ b, Fin (l b)) => hbR z.1
  have hslotsP := idealGroupedSlot_card_source k m hk hcardP
  have hslotsR := idealGroupedSlot_card_source l m hl hcardR
  have hμ : ∀ x, 0 ≤ μ x := idealSelectedMass_nonneg P' (fun z => hv₀.trans_le (hVP z.1))
  have hν : ∀ y, 0 ≤ ν y := idealSelectedMass_nonneg R' (fun z => hv₀.trans_le (hVR z.1))
  have hef := idealFrameEnergy_nonneg μ hμ f
  have heg := idealFrameEnergy_nonneg ν hν g
  have heps : (L^(-E))^2 = L^(-2*E) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hpiece (a : ℕ) (ha : a ∈ idealProductDyads p) (b : ℕ) (hb : b ∈ idealProductDyads q) :
      ‖∑ x, (μ x : ℂ)*idealProductDyadicPart p a f x*
        ∑ y, (ν y : ℂ)*idealProductDyadicPart q b g y*K x y‖^2 ≤
      (L^(-E))^2*idealFrameEnergy μ (idealProductDyadicPart p a f)*
        idealFrameEnergy ν (idealProductDyadicPart q b g) := by
    have hpa := horiginP (Σ a, Fin (k a)) P' hpP hboundsP hslotsP i a ha
    have hqb := horiginR (Σ b, Fin (l b)) R' hpR hboundsR hslotsR j b hb
    have hp := hdyad A B P k R l hP hR hdisP hdisR hVP hVR hk hl hcardP hcardR hbP hbR i j hi hj
      (idealProductDyadicOrigin a) (idealProductDyadicOrigin b) hpa.1 hqb.1 hpa.2.1 hqb.2.1 hpa.2.2 hqb.2.2
      ζ α hζ (idealProductDyadicPart p a f) (idealProductDyadicPart q b g)
      (idealSelectedProductDyadicPart_origin_support P' hpP i ha f)
      (idealSelectedProductDyadicPart_origin_support R' hpR j hb g)
    rw [heps]
    exact hp
  have hsum := idealDyadicPairing_sq_le p q μ ν hμ hν f g K (L^(-E)) hpiece
  have hcp := hcountP (Σ a, Fin (k a)) P' hpP (fun z p hp => (hboundsP z p hp).2) hslotsP
  have hcq := hcountR (Σ b, Fin (l b)) R' hpR (fun z p hp => (hboundsR z p hp).2) hslotsR
  have hcoefficient : ((idealProductDyads p).card : ℝ)^2*((idealProductDyads q).card : ℝ)^2*
      (L^(-E))^2 ≤ L^(-2*A₀) := by
    calc
      _ ≤ (L^(d+3))^2*(L^(d+3))^2*(L^(-E))^2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hcp 2)
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hcq 2) (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      _ = L^(-2*A₀-2) := by
        rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hL.le, heps, ← Real.rpow_add hL]
        congr 1
        dsimp [E, idealComparisonPrecision]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hsq : ‖∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*K x y‖^2 ≤
      L^(-2*A₀)*idealFrameEnergy μ f*idealFrameEnergy ν g := hsum.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient hef) heg)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ L^(-A₀)*Real.sqrt (idealFrameEnergy μ f)*Real.sqrt (idealFrameEnergy ν g))).mp
  calc
    _ ≤ L^(-2*A₀)*idealFrameEnergy μ f*idealFrameEnergy ν g := hsq
    _ = (L^(-A₀)*Real.sqrt (idealFrameEnergy μ f)*Real.sqrt (idealFrameEnergy ν g))^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hef, Real.sq_sqrt heg, ← Real.rpow_two, ← Real.rpow_mul hL.le]
      rw [show (-A₀)*2 = -2*A₀ by ring]

end
end ArtinMatthews
