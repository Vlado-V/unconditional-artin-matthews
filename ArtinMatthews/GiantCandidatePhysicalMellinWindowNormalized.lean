module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantTwoSidedPhysicalMellinPairing
public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.GiantCandidateRetainedSourceScalars
public import ArtinMatthews.GiantPhysicalMellinLogSaving
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

/-! The normalized retained pairing gives the same exponent in the Mellin
window. The reciprocal position and Mellin phase modify only the left mask. -/
namespace ArtinMatthews
open Filter Set
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v

theorem giantCandidatePhysicalMellinWindow_normalized_eventually {Jtest : Type*} [Fintype Jtest]
    (e : Jtest → ℝ) (ε γ : ℝ) {mχ : ℕ} (χ : DirichletCharacter ℂ mχ)
    (j : ℕ) (B C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let L := Real.log x
      ∀ {I : Type u} {J : Type v} [Fintype J] [DecidableEq J]
        {P : J → Finset ℕ} {k ell : ℕ}
        (patterns : Finset I) (copied : I → J → Finset (Fin k)) (step : ℤ) (q : ℝ)
        (K : ∀ p, GiantTwoSidedPatternCoefficient P (copied p) ell) {X : ℝ}, 0 < X →
      let roots := giantTwoSidedRootInterval X
      let Z := giantTwoSidedRootSlice X
      let F (u : ℕ → ℂ) (r : ℕ) :=
        if r ∈ roots then u r*conj (giantCandidateFirstEndpoint e ε x r) else 0
      let G (v : ℕ → ℂ) (r : ℕ) := v r*(χ r*giantCandidateAllocationCore
        (giantCandidateFullPrimes x) (Finset.univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r)
      let damp (r : ℕ) := (giantTwoSidedEndpointDamping P (k+ell) q r : ℂ)
      let left (u : ℕ → ℂ) (r : ℕ) := damp r*F u r
      let right (v : ℕ → ℂ) (s : GiantTwoSidedEndpointState P (k+ell) Z) :=
        damp s.val.1.val*G v s.val.1.val
      (∀ ζ : ℝ, |ζ| ≤ L^(C+1) →
        ∀ u v : ℕ → ℂ, (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
        ‖giantTwoSidedPhysicalWeightedPairing
          (giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns copied step q ζ K)
          (fun s => left u s.val.1.val) (right v)/(X : ℂ)‖ ≤ L^(-B)) →
      ∀ u v : ℕ → ℂ, (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
      ∀ t ∈ Icc (-(L^C)) (L^C),
        ‖giantTwoSidedPhysicalWeightedPairing
          (giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns copied step q (0-2*Real.pi*t) K)
          (giantTwoSidedPhysicalMellinLeft t (left u)) (right v)‖ ≤ L^(-B) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.pi)] with x hL
  intro L I J _ _ P k ell patterns copied step q K X hX roots Z F G damp left right
    hpair u v hu hv t ht
  have hπ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hL₀ : 0 < L := hπ.trans_le hL
  have hζ : |0-2*Real.pi*t| ≤ L^(C+1) := by
    rw [zero_sub,abs_neg,abs_mul,abs_of_nonneg hπ.le,Real.rpow_add hL₀,Real.rpow_one]
    exact (mul_le_mul hL (abs_le.mpr ht) (abs_nonneg t) hL₀.le).trans_eq (mul_comm L (L^C))
  let w (r : ℕ) := ((X : ℂ)/(r : ℂ))*(primeExtractionMellinPhase (-t) (r : ℝ)*u r)
  have hw : ∀ r ∈ roots, ‖w r‖ ≤ 1 := by
    intro r hr
    apply giantTwoSidedRootInterval_reciprocal_norm_le_one hX hr
    simpa only [norm_mul,primeExtractionMellinPhase_norm,one_mul] using hu r hr
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  have hleft : giantTwoSidedPhysicalMellinLeftNormalized X t (left u) =
      fun s : State => left w s.val.1.val := by
    funext s
    let r := s.val.1.val
    change ((X/(r : ℝ) : ℝ) : ℂ)*primeExtractionMellinPhase (-t) (r : ℝ)*left u r = left w r
    rw [Complex.ofReal_div,Complex.ofReal_natCast]
    by_cases hr : r ∈ roots
    · simp only [left,F,w,hr,ite_true]
      ring
    · simp only [left,F,hr,ite_false,mul_zero]
  let A := giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns copied step q (0-2*Real.pi*t) K
  have h : ‖giantTwoSidedPhysicalWeightedPairing A (fun s : State => left w s.val.1.val)
      (right v)/(X : ℂ)‖ ≤ L^(-B) := hpair _ hζ w v hw hv
  rw [← hleft,giantTwoSidedPhysicalMellinPairing_normalized_eq A (left u) (right v) hX t] at h
  exact h

end
end ArtinMatthews
