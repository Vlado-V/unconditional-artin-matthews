module

public import ArtinMatthews.IdealMajorBilinearUniform
public import ArtinMatthews.IdealMinorBilinearUniform
public import ArtinMatthews.IdealDirichletApprox
public import ArtinMatthews.IdealGroupedSlotCount
public import ArtinMatthews.IdealMinorSourceGeometry
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

/-! The actual character/log-cell comparison on a source product dyad
holds at every real additive frequency, with one fixed kernel. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def idealComparisonWidth (m : ℕ) (C₀ v₀ d C E : ℝ) : ℝ :=
  let a := idealMinorBilinearExponent m C₀ v₀ d E
  idealMajorBilinearWidth a a C E

def idealComparisonThreshold (m : ℕ) (C₀ v₀ d C E : ℝ) : ℝ :=
  let a := idealMinorBilinearExponent m C₀ v₀ d E
  idealMajorBilinearThreshold a a C d E

theorem idealCharacterDyad_comparison (m : ℕ) (C₀ v₀ c d C E : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d)
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
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
      ∀ U V : ℕ, 0 < U → 0 < V → Real.exp (L^c)/4 ≤ (U : ℝ) → Real.exp (L^c)/4 ≤ (V : ℝ) →
      Real.log (U : ℝ) ≤ L^(d+2) → Real.log (V : ℝ) ≤ L^(d+2) →
      ∀ (ζ α : ℝ), |ζ| ≤ L^C →
      ∀ (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
        (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ),
      (∀ x, idealSelectedProduct x ∉ Ico (2*U) (4*U) → f x = 0) →
      (∀ y, idealSelectedProduct y ∉ Ico (2*V) (4*V) → g y = 0) →
      ‖∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
        ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
          (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
            idealFullCellPhaseAverage (fun z : Σ i, Fin (k i) => P z.1)
              (fun z : Σ i, Fin (l i) => R z.1) ⌊L^(idealMinorBilinearExponent m C₀ v₀ d E)⌋₊
              (L^(-idealComparisonWidth m C₀ v₀ d C E))
              (L^(-idealComparisonThreshold m C₀ v₀ d C E)) ζ α x y)‖^2 ≤
        L^(-2*E)*idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f*
          idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g := by
  let a := idealMinorBilinearExponent m C₀ v₀ d E
  let H := idealComparisonWidth m C₀ v₀ d C E
  let X := idealComparisonThreshold m C₀ v₀ d C E
  have hκ := idealGroupedBudgetExponent_nonneg m (v₀ := v₀) hC₀
  have ha : 0 ≤ a := by dsimp [a, idealMinorBilinearExponent, idealMinorCutoffExponent]; linarith
  have hH : 1 ≤ H := by
    dsimp [H, idealComparisonWidth, idealMajorBilinearWidth, idealMajorCellExponent]
    change 1 ≤ 4*a+a+C+(E+2)+4
    linarith
  have hX : 0 ≤ X := by
    change 0 ≤ idealDiscardedThresholdExponent d H E
    dsimp [idealDiscardedThresholdExponent]
    linarith
  filter_upwards [idealMajorCellBilinear_uniform.{u,v} a c d a C E ((m : ℝ)*C₀) v₀
      ha hc hd ha hC hE hv₀,
    idealMinorCellBilinear_uniform.{u,v} m C₀ v₀ c d E X H hC₀ hv₀ hc hd hE hX hH,
    idealSource_rational_scale a c hc, eventually_ge_atTop (2 : ℝ)] with L hmajor hminor hscale hL2
  have hL : 0 < L := by linarith
  have hpow : 0 < L^a := Real.rpow_pos_of_pos hL _
  intro A B _ _ _ _ P k R l hP hR hdisP hdisR hVP hVR hk hl hcardP hcardR hbP hbR i j hi hj
    U V hU hV hUl hVl hUlog hVlog ζ α hζ f g hf hg
  let Q := ⌊L^a⌋₊
  have hQ : (Q : ℝ) ≤ L^a := Nat.floor_le hpow.le
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  obtain ⟨w, r, β, hr, hcop, hrup, hα, hβ, hβscale⟩ :=
    idealDirichletApprox α (16*(U : ℝ)*(V : ℝ)) (L^a) hpow (hscale U V hUl hVl)
  let _ : NeZero r := ⟨hr.ne'⟩
  have hvP : ∀ i, 0 < bandReciprocalMass (P i) := fun i => hv₀.trans_le (hVP i)
  have hvR : ∀ i, 0 < bandReciprocalMass (R i) := fun i => hv₀.trans_le (hVR i)
  by_cases hsmall : r ≤ Q
  · have hβall (x : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1))
        (y : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1)) (hx : f x ≠ 0) (hy : g y ≠ 0) :
        |β| * (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ) ≤ L^a := by
      have hmx : idealSelectedProduct x ∈ Ico (2*U) (4*U) := by
        by_contra hh
        exact hx (hf x hh)
      have hmy : idealSelectedProduct y ∈ Ico (2*V) (4*V) := by
        by_contra hh
        exact hy (hg y hh)
      have hpx : (idealSelectedProduct x : ℝ) ≤ 4*(U : ℝ) := by exact_mod_cast (mem_Ico.mp hmx).2.le
      have hpy : (idealSelectedProduct y : ℝ) ≤ 4*(V : ℝ) := by exact_mod_cast (mem_Ico.mp hmy).2.le
      calc
        _ ≤ |β| * (4*(U : ℝ))*(4*(V : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpx (abs_nonneg _)) hpy
            (Nat.cast_nonneg _) (by positivity)
        _ = |β| * (16*(U : ℝ)*(V : ℝ)) := by ring
        _ ≤ L^a/(r : ℝ) := hβscale
        _ ≤ L^a := div_le_self hpow.le (by exact_mod_cast hr)
    have hm := hmajor (Σ a, Fin (k a)) (Σ b, Fin (l b)) Q r hQ hsmall
      (fun z => P z.1) (fun z => R z.1) (fun z p hp => hP z.1 p hp) (fun z p hp => hR z.1 p hp)
      (fun z => hvP z.1) (fun z => hvR z.1) (fun z => hbP z.1) (fun z => hbR z.1)
      (idealGroupedSlot_card_source k m hk hcardP) (idealGroupedSlot_card_source l m hl hcardR)
      i j hi hj (hVP i.1) (hVR j.1) w ζ β f g hζ hβall
    rw [← hα] at hm
    exact hm
  · have hrlarge : L^a < (r : ℝ) := (Nat.floor_lt hpow.le).mp (lt_of_not_ge hsmall)
    have hrlower : L^a/2 ≤ (r : ℝ) := by linarith
    have hrupper : (r : ℝ) ≤ 64*(U : ℝ)*(V : ℝ)/L^a := hrup.trans
      (div_le_div_of_nonneg_right (by nlinarith) hpow.le)
    have happrox : |α-(w : ℝ)/r| ≤ 1/(r : ℝ)^2 := by
      have he : α-(w : ℝ)/r = β := by rw [hα]; ring
      rw [he]
      exact hβ
    exact hminor A B P k R l hP hR hdisP hdisR hVP hVR hk hl hcardP hcardR hbP hbR i j hi hj Q hQ
      U V r hU hV hr hUl hVl hUlog hVlog hrlower hrupper ζ α w hcop happrox f g hf hg

end
end ArtinMatthews
