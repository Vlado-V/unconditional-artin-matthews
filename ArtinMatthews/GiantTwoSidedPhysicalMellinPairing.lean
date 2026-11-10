module

public import ArtinMatthews.GiantTwoSidedPhysicalPairing
public import ArtinMatthews.GiantPhysicalMellin
public import ArtinMatthews.GiantPhysicalMellinBound
public import ArtinMatthews.GiantPhysicalMellinCoefficient
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

/-! Exact Mellin separation of the complete finite physical family. The
source dilation uses the permuted left marks and the actual auxiliary labels. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {Z : Finset ℕ} {patterns : Finset I} {C : I → J → Finset (Fin k)}

def giantTwoSidedPhysicalChoiceDilation
    (c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
    (s : GiantTwoSidedEndpointState P (k+ell) Z) : ℕ :=
  giantTwoSidedPatternDilation (C c.1.val)
    (giantTwoSidedEndpointPermute c.2.1 s).val.2 c.2.2.2

theorem giantTwoSidedPhysicalChoiceDilation_pos
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
    (s : GiantTwoSidedEndpointState P (k+ell) Z) :
    0 < giantTwoSidedPhysicalChoiceDilation c s :=
  giantTwoSidedPatternDilation_pos hP _ _ _

def giantTwoSidedPhysicalMellinLeft {M : ℕ} (v : ℝ) (f : ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P M Z) : ℂ :=
  primeExtractionMellinPhase (-v) (s.val.1.val : ℝ)/(s.val.1.val : ℂ)*f s.val.1.val

theorem giantTwoSidedPhysicalMellinLeft_star {M : ℕ} (v : ℝ) (f : ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P M Z) :
    star (giantTwoSidedPhysicalMellinLeft v f s) =
      primeExtractionMellinPhase v (s.val.1.val : ℝ)/(s.val.1.val : ℂ)*star (f s.val.1.val) := by
  simp only [giantTwoSidedPhysicalMellinLeft,star_mul,star_div₀,
    giantPhysicalMellinPhase_conj,neg_neg,star_natCast]
  exact mul_comm _ _

theorem giantTwoSidedPhysicalChoiceCoefficient_mellin
    (hP : ∀ j p, p ∈ P j → p.Prime) (step : ℤ) (q ζ v : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z) :
    giantTwoSidedPhysicalChoiceCoefficient step q (ζ-2*Real.pi*v) K c s t =
      giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t*
        primeExtractionMellinPhase (-v) (giantTwoSidedPhysicalChoiceDilation c s : ℝ) := by
  simpa only [giantTwoSidedPhysicalChoiceCoefficient,giantTwoSidedPhysicalChoiceDilation,
    giantTwoSidedPatternDilation,Nat.cast_mul] using
    giantTwoSidedPatternPhysicalCoefficient_mellin hP step q ζ v (K c.1.val)
      (giantTwoSidedEndpointPermute c.2.1 s) (giantTwoSidedEndpointPermute c.2.2.1 t) c.2.2.2

def giantTwoSidedPhysicalCutoffPairing
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)*
      ∑ c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell, ∑ s, ∑ t,
        giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t*
          (Ψ ((s.val.1.val : ℝ)/(x*(giantTwoSidedPhysicalChoiceDilation c s : ℝ)))/
            (s.val.1.val : ℂ))*star (f s.val.1.val)*g t

local notation "State" => GiantTwoSidedEndpointState P (k+ell) Z
local notation "Choice" => GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
local notation "Edge" => Choice × State × State

private def physicalMellinEdgeWeight
    (step : ℤ) (q ζ : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (f : ℕ → ℂ) (g : State → ℂ) (e : Edge) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)*
    giantTwoSidedPhysicalChoiceCoefficient step q ζ K e.1 e.2.1 e.2.2/
      (e.2.1.val.1.val : ℂ)*star (f e.2.1.val.1.val)*g e.2.2

private theorem cutoff_eq_edge_sum (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f : ℕ → ℂ) (g : State → ℂ) :
    giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g =
      ∑ e : Edge, physicalMellinEdgeWeight step q ζ K f g e*
        Ψ ((e.2.1.val.1.val : ℝ)/(x*(giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ))) := by
  simp only [giantTwoSidedPhysicalCutoffPairing,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [physicalMellinEdgeWeight]
  ring

private theorem edge_mellin_sum_eq_pairing (hP : ∀ j p, p ∈ P j → p.Prime)
    (step : ℤ) (q ζ v : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (f : ℕ → ℂ) (g : State → ℂ) :
    giantPhysicalMellinSum (Finset.univ : Finset Edge) (physicalMellinEdgeWeight step q ζ K f g)
        (fun e => (e.2.1.val.1.val : ℝ))
        (fun e => (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)) v =
      giantTwoSidedPhysicalWeightedPairing
        (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
        (giantTwoSidedPhysicalMellinLeft v f) g := by
  rw [giantTwoSidedPhysicalWeightedPairing_expand]
  simp only [giantPhysicalMellinSum,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [giantTwoSidedPhysicalChoiceCoefficient_mellin hP step q ζ v K c s t,
    giantTwoSidedPhysicalMellinLeft_star]
  dsimp only [physicalMellinEdgeWeight]
  ring

theorem giantTwoSidedPhysicalCutoffPairing_mellin
    (hP : ∀ j p, p ∈ P j → p.Prime) (hZ : ∀ n ∈ Z, 0 < n)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) {x : ℝ} (hx : 0 < x) (f : ℕ → ℂ) (g : State → ℂ) :
    giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g =
      ∫ v : ℝ, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v*
        primeExtractionMellinPhase (-v) x*
        giantTwoSidedPhysicalWeightedPairing
          (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
          (giantTwoSidedPhysicalMellinLeft v f) g := by
  rw [cutoff_eq_edge_sum]
  rw [giantPhysicalMellin_cutoff _ _ _ _ Ψ ha hsupp hΨ hx
    (fun e _ => Nat.cast_pos.mpr (hZ _ e.2.1.val.1.property))
    (fun e _ => Nat.cast_pos.mpr (giantTwoSidedPhysicalChoiceDilation_pos hP e.1 e.2.1))]
  simp only [edge_mellin_sum_eq_pairing hP]

theorem giantTwoSidedPhysicalMellinLeft_norm {M : ℕ} (v : ℝ) (f : ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P M Z) :
    ‖giantTwoSidedPhysicalMellinLeft v f s‖ = ‖f s.val.1.val‖/(s.val.1.val : ℝ) := by
  rw [giantTwoSidedPhysicalMellinLeft,norm_mul,norm_div,primeExtractionMellinPhase_norm,
    Complex.norm_natCast]
  ring

def giantTwoSidedPhysicalMellinAbsoluteMass
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (f : ℕ → ℂ) (g : State → ℂ) : ℝ :=
  ∑ c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell, ∑ s, ∑ t,
    ‖(markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
      (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)*
      giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t/(s.val.1.val : ℂ)*
      star (f s.val.1.val)*g t‖

private theorem edge_norm_eq_absolute_mass (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (f : ℕ → ℂ) (g : State → ℂ) :
    (∑ e : Edge, ‖physicalMellinEdgeWeight step q ζ K f g e‖) =
      giantTwoSidedPhysicalMellinAbsoluteMass patterns C step q ζ K f g := by
  simp only [Fintype.sum_prod_type,physicalMellinEdgeWeight,giantTwoSidedPhysicalMellinAbsoluteMass]

theorem giantTwoSidedPhysicalMellinPairing_integrable
    (hP : ∀ j p, p ∈ P j → p.Prime) (hZ : ∀ n ∈ Z, 0 < n)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (F : SchwartzMap ℝ ℂ)
    {x : ℝ} (hx : 0 < x) (f : ℕ → ℂ) (g : State → ℂ) :
    Integrable (fun v : ℝ => F v*primeExtractionMellinPhase (-v) x*
      giantTwoSidedPhysicalWeightedPairing
        (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
        (giantTwoSidedPhysicalMellinLeft v f) g) := by
  let E := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell × State × State
  have h := giantPhysicalMellin_integrable (Finset.univ : Finset E)
      (physicalMellinEdgeWeight (patterns := patterns) (C := C) step q ζ K f g)
      (fun e => (e.2.1.val.1.val : ℝ))
      (fun e => (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)) F hx
      (fun e _ => Nat.cast_pos.mpr (hZ _ e.2.1.val.1.property))
      (fun e _ => Nat.cast_pos.mpr (giantTwoSidedPhysicalChoiceDilation_pos hP e.1 e.2.1))
  refine h.congr (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [edge_mellin_sum_eq_pairing (patterns := patterns) (C := C) hP step q ζ v K f g]

theorem giantTwoSidedPhysicalCutoffPairing_mellin_truncation
    (hP : ∀ j p, p ∈ P j → p.Prime) (hZ : ∀ n ∈ Z, 0 < n)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) (j : ℕ)
    (f : ℕ → ℂ) (g : State → ℂ) :
    ‖giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g -
      ∫ v : ℝ in Icc (-H) H, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v*
        primeExtractionMellinPhase (-v) x*
        giantTwoSidedPhysicalWeightedPairing
          (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
          (giantTwoSidedPhysicalMellinLeft v f) g‖ ≤
      ((∫ v : ℝ, |v|^j*‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v‖)/H^j)*
        giantTwoSidedPhysicalMellinAbsoluteMass patterns C step q ζ K f g := by
  let E := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell × State × State
  have h := giantPhysicalMellin_cutoff_truncation (Finset.univ : Finset E)
    (physicalMellinEdgeWeight (patterns := patterns) (C := C) step q ζ K f g)
    (fun e => (e.2.1.val.1.val : ℝ))
    (fun e => (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)) Ψ ha hsupp hΨ hx hH j
    (fun e _ => Nat.cast_pos.mpr (hZ _ e.2.1.val.1.property))
    (fun e _ => Nat.cast_pos.mpr (giantTwoSidedPhysicalChoiceDilation_pos hP e.1 e.2.1))
  rw [← cutoff_eq_edge_sum (patterns := patterns) (C := C) step q ζ K Ψ x f g,
    edge_norm_eq_absolute_mass (patterns := patterns) (C := C) step q ζ K f g] at h
  have hi : (∫ v : ℝ in Icc (-H) H, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v*
      primeExtractionMellinPhase (-v) x*
      giantPhysicalMellinSum (Finset.univ : Finset E)
        (physicalMellinEdgeWeight (patterns := patterns) (C := C) step q ζ K f g)
        (fun e => (e.2.1.val.1.val : ℝ))
        (fun e => (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)) v) =
      ∫ v : ℝ in Icc (-H) H, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v*
        primeExtractionMellinPhase (-v) x*
        giantTwoSidedPhysicalWeightedPairing
          (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
          (giantTwoSidedPhysicalMellinLeft v f) g := by
    apply integral_congr_ae
    exact Eventually.of_forall fun v => by
      dsimp only
      rw [edge_mellin_sum_eq_pairing (patterns := patterns) (C := C) hP step q ζ v K f g]
  rw [hi] at h
  exact h

theorem giantTwoSidedPhysicalCutoffPairing_mellin_norm_le
    (hP : ∀ j p, p ∈ P j → p.Prime) (hZ : ∀ n ∈ Z, 0 < n)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) {x H R : ℝ} (hx : 0 < x) (hH : 0 < H) (hR : 0 ≤ R) (j : ℕ)
    (f : ℕ → ℂ) (g : State → ℂ)
    (hbound : ∀ v ∈ Icc (-H) H, ‖giantTwoSidedPhysicalWeightedPairing
      (giantTwoSidedPhysicalFamilyMatrix patterns C step q (ζ-2*Real.pi*v) K)
      (giantTwoSidedPhysicalMellinLeft v f) g‖ ≤ R) :
    ‖giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g‖ ≤
      (∫ v : ℝ, ‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v‖)*R +
      ((∫ v : ℝ, |v|^j*‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v‖)/H^j)*
        giantTwoSidedPhysicalMellinAbsoluteMass patterns C step q ζ K f g := by
  let E := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell × State × State
  have h := giantPhysicalMellin_cutoff_norm_le (Finset.univ : Finset E)
    (physicalMellinEdgeWeight (patterns := patterns) (C := C) step q ζ K f g)
    (fun e => (e.2.1.val.1.val : ℝ))
    (fun e => (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ)) Ψ ha hsupp hΨ hx hH hR j
    (fun e _ => Nat.cast_pos.mpr (hZ _ e.2.1.val.1.property))
    (fun e _ => Nat.cast_pos.mpr (giantTwoSidedPhysicalChoiceDilation_pos hP e.1 e.2.1))
    (fun v hv => by
      rw [edge_mellin_sum_eq_pairing (patterns := patterns) (C := C) hP step q ζ v K f g]
      exact hbound v hv)
  rw [← cutoff_eq_edge_sum (patterns := patterns) (C := C) step q ζ K Ψ x f g,
    edge_norm_eq_absolute_mass (patterns := patterns) (C := C) step q ζ K f g] at h
  exact h

end
end ArtinMatthews
