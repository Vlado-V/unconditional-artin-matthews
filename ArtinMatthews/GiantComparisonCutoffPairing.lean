module

public import ArtinMatthews.GiantTwoSidedPhysicalResidualExpansion
public import ArtinMatthews.GiantComparisonStripKernel
public import ArtinMatthews.GiantComparisonStripSum
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

/-! The actual comparison cutoff pairing is the finite physical sum.
Its two normalized slot averages only rename the endpoint states. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell N m : ℕ} {C : J → Finset (Fin k)} {Z : Finset ℕ}

def giantComparisonCharacterCoefficient (χ : DirichletCharacter ℂ m)
    (K : GiantTwoSidedPatternCoefficient P C ell) :
    GiantTwoSidedPatternCoefficient P C ell :=
  fun a b aux => K a b aux * conj (χ (giantTwoSidedPatternDilation C a aux : ℕ))

theorem giantComparisonCharacterCoefficient_physical (step : ℤ) (q ζ : ℝ)
    (χ : DirichletCharacter ℂ m) (K : GiantTwoSidedPatternCoefficient P C ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z)
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternPhysicalCoefficient step q ζ (giantComparisonCharacterCoefficient χ K) s t aux =
      giantTwoSidedPatternPhysicalCoefficient step q ζ K s t aux *
        conj (χ (giantTwoSidedPatternDilation C s.val.2 aux : ℕ)) := by
  unfold giantTwoSidedPatternPhysicalCoefficient
  split_ifs <;> simp only [giantComparisonCharacterCoefficient, zero_mul] <;> ring

theorem giantComparisonCutoffPairing_eq_sum (C : J → Finset (Fin k))
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell) :
    giantTwoSidedPhysicalPatternCutoffPairing (Z:=Z) C 1 q 0
        (giantComparisonCharacterCoefficient χ K) Ψ x
        (fun n => (giantTwoSidedEndpointDamping P (k+ell) q n : ℂ)*conj (F n))
        (fun t => (giantTwoSidedEndpointDamping P (k+ell) q t.val.1.val : ℂ)*
          χ t.val.1.val*G t.val.1.val) =
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
        giantComparisonPhysicalSummand x q Ψ χ F G K s t aux := by
  classical
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Permutations := J → Equiv.Perm (Fin (k+ell))
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  let ν : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  let left (n : ℕ) := (giantTwoSidedEndpointDamping P (k+ell) q n : ℂ)*conj (F n)
  let right (t : State) := (giantTwoSidedEndpointDamping P (k+ell) q t.val.1.val : ℂ)*
    χ t.val.1.val*G t.val.1.val
  let term (s t : State) (aux : GiantTwoSidedPatternAuxiliary P C) :=
    giantTwoSidedPatternPhysicalCoefficient 1 q 0 (giantComparisonCharacterCoefficient χ K) s t aux *
      (Ψ ((s.val.1.val:ℝ)/(x*(giantTwoSidedPatternDilation C s.val.2 aux:ℝ)))/(s.val.1.val:ℂ)) *
      star (left s.val.1.val) * right t
  have hterm (s t : State) (aux : GiantTwoSidedPatternAuxiliary P C) :
      σ*term s t aux = giantComparisonPhysicalSummand x q Ψ χ F G K s t aux := by
    simp only [term, left, right, σ, giantComparisonCharacterCoefficient_physical,
      giantComparisonPhysicalSummand, giantTwoSidedPatternDilation, Complex.star_def, map_mul,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hsum (π τ : Permutations) :
      (∑ aux : GiantTwoSidedPatternAuxiliary P C, ∑ s : State, ∑ t : State,
          term (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t) aux) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C, ∑ s : State, ∑ t : State, term s t aux := by
    apply sum_congr rfl
    intro aux _
    calc
      _ = ∑ s : State, ∑ t : State, term (giantTwoSidedEndpointPermute π s) t aux :=
        sum_congr rfl (fun s _ => (giantTwoSidedEndpointPermute τ).sum_comp
          (fun t => term (giantTwoSidedEndpointPermute π s) t aux))
      _ = _ := (giantTwoSidedEndpointPermute π).sum_comp (fun s => ∑ t : State, term s t aux)
  let c : ℂ := Fintype.card Permutations
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr
    (Fintype.card_pos_iff.mpr ⟨fun _ => Equiv.refl _⟩).ne'
  have hν : ν = (c^2)⁻¹ := by
    simp only [ν, c, giantTwoSidedResidueSlotNormalization, Complex.ofReal_inv,
      Complex.ofReal_pow, Complex.ofReal_natCast, Permutations]
  change σ*ν*(∑ π : Permutations, ∑ τ : Permutations,
    ∑ aux : GiantTwoSidedPatternAuxiliary P C, ∑ s : State, ∑ t : State,
      term (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t) aux) = _
  simp_rw [hsum]
  simp only [sum_const, nsmul_eq_mul, card_univ]
  rw [hν, mul_assoc σ]
  change σ*((c^2)⁻¹*(c*(c*∑ aux, ∑ s : State, ∑ t : State, term s t aux))) = _
  rw [← mul_assoc c c, ← pow_two, inv_mul_cancel_left₀ (pow_ne_zero _ hc)]
  simp only [Finset.mul_sum, hterm]
  rfl

theorem giantComparisonCutoffPairing_eq_shared
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N)
    (C : J → Finset (Fin k)) {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (hF : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      F (giantComparisonSharedProduct c*w) = F w)
    (hG : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      G (giantComparisonSharedProduct c*w) = G w)
    (hc : ∀ c : GiantComparisonSharedLabels P C, (giantComparisonSharedProduct c).Coprime m) :
    giantTwoSidedPhysicalPatternCutoffPairing (Z:=Z) C 1 q 0
        (giantComparisonCharacterCoefficient χ K) Ψ x
        (fun n => (giantTwoSidedEndpointDamping P (k+ell) q n : ℂ)*conj (F n))
        (fun t => (giantTwoSidedEndpointDamping P (k+ell) q t.val.1.val : ℂ)*
          χ t.val.1.val*G t.val.1.val) =
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ a : GiantComparisonSharedEdge P C ell N Z Z aux,
        giantComparisonSharedSummand x q Ψ χ F G K a := by
  rw [giantComparisonCutoffPairing_eq_sum]
  exact giantComparisonPhysical_sum_eq_shared hP hdis hZ hx q Ψ χ F G K hF hG hc

end
end ArtinMatthews
