module

public import ArtinMatthews.GiantComparisonCutoffPairing
public import ArtinMatthews.SourceCharacterPairingFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The character on the actual positive-step dilation separates into
finite additive phases at the two physical endpoints. -/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell M : ℕ} [NeZero M] {Z : Finset ℕ}
  {patterns : Finset I} {C : I → J → Finset (Fin k)}

local notation "State" => GiantTwoSidedEndpointState P (k+ell) Z
local notation "Choice" => GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell

private theorem physicalChoice_character_fourier (q ζ : ℝ) (χ : DirichletCharacter ℂ M)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (c : Choice) (s t : State) :
    giantTwoSidedPhysicalChoiceCoefficient 1 q ζ
        (fun p => giantComparisonCharacterCoefficient χ (K p)) c s t =
      giantTwoSidedPhysicalChoiceCoefficient 1 q ζ K c s t *
        ∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r) *
          giantCharacterEndpointPhase r s.val.1.val *
          conj (giantCharacterEndpointPhase r t.val.1.val) := by
  unfold giantTwoSidedPhysicalChoiceCoefficient
  rw [giantComparisonCharacterCoefficient_physical]
  by_cases h : GiantTwoSidedPatternCondition (C c.1.val) 1
      (giantTwoSidedEndpointPermute c.2.1 s) (giantTwoSidedEndpointPermute c.2.2.1 t) c.2.2.2
  · have hstep := h.2.1
    change (t.val.1.val:ℤ) = (s.val.1.val:ℤ) + 1*(giantTwoSidedPhysicalChoiceDilation c s:ℤ) at hstep
    rw [one_mul] at hstep
    have hn : t.val.1.val = s.val.1.val + giantTwoSidedPhysicalChoiceDilation c s := by
      exact_mod_cast hstep
    have horder : s.val.1.val ≤ t.val.1.val := hn ▸ Nat.le_add_right _ _
    have hd : t.val.1.val - s.val.1.val = giantTwoSidedPhysicalChoiceDilation c s := by
      rw [hn, Nat.add_sub_cancel_left]
    have hχ := giant_character_conj_nat_difference_expansion χ s.val.1.val t.val.1.val horder
    rw [hd] at hχ
    change _ * conj (χ (giantTwoSidedPhysicalChoiceDilation c s : ℕ)) = _
    rw [hχ]
  · simp only [giantTwoSidedPatternPhysicalCoefficient, if_neg h, zero_mul]

/-- The exact family cutoff with a character on the dilation is a finite
linear combination of the same cutoff with phased endpoints. -/
theorem giantTwoSidedPhysicalCutoffPairing_character_fourier
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (q ζ : ℝ)
    (χ : DirichletCharacter ℂ M) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ) (g : State → ℂ) :
    giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ
        (fun p => giantComparisonCharacterCoefficient χ (K p)) Ψ x f g =
      ∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r) *
        giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ K Ψ x
          (fun n => conj (giantCharacterEndpointPhase r n) * f n)
          (fun t => conj (giantCharacterEndpointPhase r t.val.1.val) * g t) := by
  classical
  let Edge := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell × State × State
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  let ν : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  let Kχ := fun p => giantComparisonCharacterCoefficient χ (K p)
  let left (r : ZMod M) (n : ℕ) := conj (giantCharacterEndpointPhase r n) * f n
  let right (r : ZMod M) (t : State) := conj (giantCharacterEndpointPhase r t.val.1.val) * g t
  let coeff (r : ZMod M) := conj (giantCharacterAdditiveCoefficient χ r)
  let term (K' : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
      (F : ℕ → ℂ) (G : State → ℂ) (e : Edge) : ℂ :=
    giantTwoSidedPhysicalChoiceCoefficient 1 q ζ K' e.1 e.2.1 e.2.2 *
      (Ψ ((e.2.1.val.1.val : ℝ)/(x*(giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)))/
        (e.2.1.val.1.val : ℂ)) * star (F e.2.1.val.1.val) * G e.2.2
  have hcutoff (K' : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
      (F : ℕ → ℂ) (G : State → ℂ) :
      giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ K' Ψ x F G =
        σ * ν * ∑ e : Edge, term K' F G e := by
    simp only [giantTwoSidedPhysicalCutoffPairing, Edge, Fintype.sum_prod_type, σ, ν, term]
  have hterm (e : Edge) : term Kχ f g e = ∑ r : ZMod M, coeff r * term K (left r) (right r) e := by
    dsimp only [term, Kχ, left, right, coeff]
    rw [physicalChoice_character_fourier]
    simp only [Finset.mul_sum, Finset.sum_mul, Complex.star_def, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  change giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ Kχ Ψ x f g =
    ∑ r : ZMod M, coeff r * giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ K Ψ x (left r) (right r)
  simp only [hcutoff, hterm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun e _ => by ring))

theorem giantTwoSidedPhysicalCutoffPairing_character_fourier_norm_le
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (q ζ : ℝ)
    (χ : DirichletCharacter ℂ M) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ) (g : State → ℂ) {R : ℝ}
    (hbound : ∀ r : ZMod M,
      ‖giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ K Ψ x
        (fun n => conj (giantCharacterEndpointPhase r n) * f n)
        (fun t => conj (giantCharacterEndpointPhase r t.val.1.val) * g t)‖ ≤ R) :
    ‖giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ
      (fun p => giantComparisonCharacterCoefficient χ (K p)) Ψ x f g‖ ≤ (M:ℝ)*R := by
  let F (r : ZMod M) := giantTwoSidedPhysicalCutoffPairing patterns C 1 q ζ K Ψ x
    (fun n => conj (giantCharacterEndpointPhase r n) * f n)
    (fun t => conj (giantCharacterEndpointPhase r t.val.1.val) * g t)
  have hR : 0 ≤ R := (norm_nonneg (F 0)).trans (hbound 0)
  rw [giantTwoSidedPhysicalCutoffPairing_character_fourier]
  change ‖∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r) * F r‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  calc
    _ ≤ ∑ r : ZMod M, ‖conj (giantCharacterAdditiveCoefficient χ r)‖ * R :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hbound r) (norm_nonneg _)
    _ = (∑ r : ZMod M, ‖conj (giantCharacterAdditiveCoefficient χ r)‖) * R := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (giant_character_conj_additive_l1_le χ) hR

end
end ArtinMatthews
