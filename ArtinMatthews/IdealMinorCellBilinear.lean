module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealGroupedAtom
public import ArtinMatthews.IdealKernelTranspose
public import ArtinMatthews.MarkedMinorArcGram
public import ArtinMatthews.IdealCellPhaseTranspose
public import ArtinMatthews.IdealCellTransposeDyadic
public import ArtinMatthews.IdealGroupedMinorBranch
public import ArtinMatthews.IdealGroupedSelectedPairing
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

/-! The exact transpose and product-fiber collapse bound the true
cell-comparison error on each enlarged minor-arc dyad. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealMinorCellBilinear_sq_le
    (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hdisP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hdisR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (Q : ℕ) {h ξ : ℝ} (hh : 0 < h) (hexp : Real.exp h ≤ 2)
    (henergyP : ∀ f, idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1))
        (idealCharacterCellTranspose (fun z : Σ i, Fin (k i) => P z.1) Q h ξ f) ≤
      4*idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f)
    (henergyR : ∀ g, idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1))
        (idealCharacterCellTranspose (fun z : Σ i, Fin (l i) => R z.1) Q h ξ g) ≤
      4*idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g)
    (U V : ℕ) (hU : 0 < U) (hV : 0 < V)
    (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
    (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ)
    (hf : ∀ x, idealSelectedProduct x ∉ Ico (2*U) (4*U) → f x = 0)
    (hg : ∀ y, idealSelectedProduct y ∉ Ico (2*V) (4*V) → g y = 0)
    (ζ α : ℝ) (u : ℤ) (r : ℕ) (hr : 0 < r) (hcop : IsCoprime u (r : ℤ))
    (happrox : |α-(u : ℝ)/r| ≤ 1/(r : ℝ)^2) :
    ‖∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
      ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
        (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
          idealFullCellPhaseAverage (fun z : Σ i, Fin (k i) => P z.1)
            (fun z : Σ i, Fin (l i) => R z.1) Q h ξ ζ α x y)‖^2 ≤
      34*markedMinorGramBudget (8*U) (8*V) r*(idealGroupedAtomBudget P k/(U : ℝ))*
        (idealGroupedAtomBudget R l/(V : ℝ))*
        idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f*
        idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g := by
  let P' := fun z : Σ i, Fin (k i) => P z.1
  let R' := fun z : Σ i, Fin (l i) => R z.1
  let F := idealCharacterCellTranspose P' Q h ξ f
  let G := idealCharacterCellTranspose R' Q h ξ g
  let μ := idealSelectedMass P'
  let ν := idealSelectedMass R'
  let phase := fun x : IdealSelectedLabels P' => fun y : IdealSelectedLabels R' =>
    idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y)
  let raw := ∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*phase x y
  let averaged := ∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*
    idealFullCellPhaseAverage P' R' Q h ξ ζ α x y
  let C := markedMinorGramBudget (8*U) (8*V) r*
    (idealGroupedAtomBudget P k/(U : ℝ))*(idealGroupedAtomBudget R l/(V : ℝ))
  let E := idealFrameEnergy μ f*idealFrameEnergy ν g
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (markedMinorGramBudget_nonneg _ _ _ hr)
      (div_nonneg (idealGroupedAtomBudget_nonneg P k hVP) (Nat.cast_nonneg _)))
      (div_nonneg (idealGroupedAtomBudget_nonneg R l hVR) (Nat.cast_nonneg _))
  have hwideP : ∀ x, idealSelectedProduct x ∉ Ico U (U+8*U) → f x = 0 := by
    intro x hx
    apply hf x
    intro hm
    apply hx
    have hb := mem_Ico.mp hm
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hwideR : ∀ y, idealSelectedProduct y ∉ Ico V (V+8*V) → g y = 0 := by
    intro y hy
    apply hg y
    intro hm
    apply hy
    have hb := mem_Ico.mp hm
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hraw : ‖raw‖^2 ≤ C*E := by
    have hb := idealSelectedGroupedPhaseBilinear_sq_le P k R l hP hR hdisP hdisR hVP hVR
      U V (8*U) (8*V) hU hV f g hwideP hwideR ζ α u r hr hcop happrox
    convert hb using 1
    dsimp [raw, μ, ν, phase, C, E]
    ring
  have hF := idealCharacterCellTranspose_dyadic_support P' (fun z p hp => hP z.1 p hp)
    Q (ξ := ξ) hh hexp U hU f hf
  have hG := idealCharacterCellTranspose_dyadic_support R' (fun z p hp => hR z.1 p hp)
    Q (ξ := ξ) hh hexp V hV g hg
  have havg : ‖averaged‖^2 ≤ 16*C*E := by
    have heq := idealFullCellPhaseAverage_pairing P' R' Q h ξ ζ α f g
    have hb := idealSelectedGroupedPhaseBilinear_sq_le P k R l hP hR hdisP hdisR hVP hVR
      U V (8*U) (8*V) hU hV F G hF hG ζ α u r hr hcop happrox
    have hEF := henergyP f
    have hEG := henergyR g
    have hf0 := idealFrameEnergy_nonneg μ (idealSelectedMass_nonneg P' (fun z => hVP z.1)) f
    rw [show averaged = ∑ x, (μ x : ℂ)*F x*∑ y, (ν y : ℂ)*G y*phase x y from heq]
    calc
      _ ≤ C*idealFrameEnergy μ F*idealFrameEnergy ν G := by
        convert hb using 1
        dsimp only [C]
        ring
      _ ≤ C*(4*idealFrameEnergy μ f)*(4*idealFrameEnergy ν g) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hEF hC) hEG
          (idealFrameEnergy_nonneg ν (idealSelectedMass_nonneg R' (fun z => hVR z.1)) G)
          (mul_nonneg hC (by positivity))
      _ = _ := by dsimp [E]; ring
  have he : (∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*
      (phase x y-idealFullCellPhaseAverage P' R' Q h ξ ζ α x y)) = raw-averaged := by
    simp only [raw, averaged, mul_sub, sum_sub_distrib]
  change ‖∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*
    (phase x y-idealFullCellPhaseAverage P' R' Q h ξ ζ α x y)‖^2 ≤ _
  rw [he]
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_sub_le raw averaged)
  have htotal : ‖raw-averaged‖^2 ≤ 34*C*E := by
    nlinarith [sq_nonneg (‖raw‖-‖averaged‖)]
  convert htotal using 1
  dsimp [C, E, μ, ν]
  ring

end
end ArtinMatthews
