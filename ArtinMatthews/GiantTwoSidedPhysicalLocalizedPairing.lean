module

public import ArtinMatthews.GiantTwoSidedPhysicalPairing
public import ArtinMatthews.GiantTwoSidedExpandedRootTransfer
public import ArtinMatthews.GiantTwoSidedPhysicalCells
public import ArtinMatthews.GiantTwoSidedPhysicalEvenMoment
public import ArtinMatthews.MarkedPhysicalEndpointNorm
public import ArtinMatthews.MarkedPositionLocalizedSubsetMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Position localization bounds the actual physical pairing by the
existing alternating root moment. Only the left vector is position-only. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantTwoSidedPhysicalPairing_localized_root {I J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime) {k ell H : ℕ} (hH : 0 < H)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (hD : ∀ p ∈ patterns, ∀ (a : MarkedPhysicalMarking P (k+ell)) aux,
      step.natAbs * giantTwoSidedPatternDilation (C p) a aux ≤ H)
    (roots Z : Finset ℕ) (hZ : roots ⊆ Z)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ)
    (hf : ∀ r ∉ roots, f r = 0) (U : ℝ) (hU : ∀ r ∈ roots, ‖f r‖ ≤ U) (r : ℕ) :
    let A := giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C step q ζ K
    let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
    let Eg := ∑ s : GiantTwoSidedEndpointState P (k+ell) Z, σ*‖g s‖^2
    let Ef := ∑ s : GiantTwoSidedEndpointState P (k+ell) Z, σ*‖f s.val.1.val‖^2
    let T := (giantTwoSidedExpandedPhysicalMoment (fun _ : Fin (2*(r+1)) => patterns) (fun _ => C)
      (fun i => if i.val%2 = 0 then step else -step) q (fun i => if i.val%2 = 0 then ζ else -ζ)
      (fun i p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) roots Z).re
    ‖giantTwoSidedPhysicalWeightedPairing A (fun s => f s.val.1.val) g‖ ≤
      Real.sqrt 3 * Real.sqrt Eg * Ef^((r:ℝ)/(2*((r+1:ℕ):ℝ))) *
        ((H : ℝ)*U^2)^((2*((r+1:ℕ):ℝ))⁻¹) * T^((2*((r+1:ℕ):ℝ))⁻¹) := by
  intro A σ Eg Ef T
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let pos (s : State) := s.val.1
  let cell := giantTwoSidedPhysicalCell (Z := Z) H
  let R : Finset ↥Z := Finset.univ.filter (fun z => z.val ∈ roots)
  have hA (s t : State) (h : A s t ≠ 0) : cell (pos t)-cell (pos s) ∈ Finset.Icc (-1 : ℤ) 1 :=
    giantTwoSidedPhysicalCell_neighbors hH (pos s) (pos t)
      (giantTwoSidedPhysicalFamilyMatrix_displacement patterns C step q ζ K hD s t h)
  have hf0 (z : ↥Z) (hz : z ∉ R) : f z.val = 0 :=
    hf z.val (fun hz' => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz'⟩))
  have hc (b : ℤ) : ((R.filter (fun z => cell z = b)).card : ℝ) ≤ (H : ℝ) := by
    apply Nat.cast_le.mpr
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ R))).trans
      (giantTwoSidedPhysicalCell_card_le Z hH b)
  have hu (z : ↥Z) (hz : z ∈ R) : ‖f z.val‖^2 ≤ U^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hU z.val (Finset.mem_filter.mp hz).2) 2
  have hmap : R.map (Function.Embedding.subtype (fun n => n ∈ Z)) = roots := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hz
      exact (Finset.mem_filter.mp hv).2
    · intro hz
      exact Finset.mem_map.mpr ⟨⟨z,hZ hz⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,rfl⟩
  have htrace : (∑ z ∈ R, markedQuadraticForm ((A*Aᴴ)^(r+1)) (markedPositionVector pos σ z)) = T := by
    calc
      _ = ∑ z ∈ R.map (Function.Embedding.subtype (fun n => n ∈ Z)),
          markedQuadraticForm ((A*Aᴴ)^(r+1)) (markedPositionVector (fun s : State => (pos s).val) σ z) := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro z _
        congr 1
        funext s
        by_cases h : (pos s).val = z.val
        · have hs : pos s = z := Subtype.ext h
          simp only [markedPositionVector, Function.Embedding.subtype_apply, h, hs, ite_true]
        · have hs : pos s ≠ z := fun he => h (congrArg Subtype.val he)
          simp only [markedPositionVector, Function.Embedding.subtype_apply, h, hs, ite_false]
      _ = T := by
        rw [hmap]
        exact giantTwoSidedPhysicalPositionTrace_eq_expanded hP patterns C step q ζ K roots Z (r+1)
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ =>
    Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)))
  let g' (s : State) := (Real.sqrt σ : ℂ)*g s
  have hEg : (∑ s, ‖g' s‖^2) = Eg := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [g', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg σ), mul_pow, Real.sq_sqrt hσ]
  have hEf : (∑ s, ‖markedPositionLift pos σ (fun z => f z.val) s‖^2) = Ef :=
    markedPositionLift_energy pos σ hσ (fun z => f z.val)
  have h := markedPositionPairing_localized_subset_moment_root A pos cell 1 (by norm_num) hA
    σ (fun z => f z.val) g' R (H : ℝ) (U^2) (Nat.cast_nonneg H) (sq_nonneg U) hf0 hc hu r
  rw [hEg,hEf,htrace] at h
  rw [giantTwoSidedPhysicalWeightedPairing_eq_scaled]
  norm_num only [Int.cast_one] at h
  exact h

end
end ArtinMatthews
