module

public import ArtinMatthews.GiantTwoSidedGroupReindexData
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor
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

/-! The numerical primes, original independent residue mean, and all
original path weights are preserved by relabeling the group indices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {A J : Type*} [Fintype A] [Fintype J] (e : A ≃ J) (P : J → Finset ℕ)

theorem giantTwoSidedIndependentResidueMean_pull
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (P ∘ e)), NeZero p.val]
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (q : ℝ) (offset : Fin (n+1) → ℤ) :
    giantTwoSidedIndependentResidueMean (fun i => giantTwoSidedPullMarking e P M (labels i)) q offset =
      giantTwoSidedIndependentResidueMean labels q offset := by
  have hpull : Pairwise (fun i j => Disjoint ((P ∘ e) i) ((P ∘ e) j)) :=
    fun _ _ h => hdis (fun he => h (e.injective he))
  unfold giantTwoSidedIndependentResidueMean
  rw [giantTwoSidedIndependentResidue_mean_product hpull,
    giantTwoSidedIndependentResidue_mean_product hdis, giantTwoSidedPull_bandPrimes e P]
  apply Finset.prod_congr rfl
  intro p hp
  letI : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : ↥(markedPhysicalBandPrimes P)).val)
  rw [giantTwoSidedIndependentPrimeMean_eq, giantTwoSidedIndependentPrimeMean_eq]
  simp only [giantTwoSidedIndependentPrimeFactor, giantTwoSidedPull_activePrimes]

theorem giantTwoSidedPull_permuteLabels {M : ℕ} (π : J → Equiv.Perm (Fin M))
    (a : MarkedPhysicalMarking P M) :
    giantTwoSidedPermuteLabels (giantTwoSidedPullSlots e M π) (giantTwoSidedPullMarking e P M a) =
      giantTwoSidedPullMarking e P M (giantTwoSidedPermuteLabels π a) := by
  funext j i
  simp only [giantTwoSidedPermuteLabels, giantTwoSidedPullMarking_apply, giantTwoSidedPullSlots_apply]

variable {k ell n : ℕ}

theorem giantTwoSidedPull_dilation (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternDilation (C ∘ e) (giantTwoSidedPullMarking e P (k+ell) a)
      (giantTwoSidedPullAuxiliary e P C aux) = giantTwoSidedPatternDilation C a aux := by
  unfold giantTwoSidedPatternDilation giantTwoSidedPatternCopiedProduct giantTwoSidedPatternAuxiliaryProduct
  simp only [Function.comp_apply, giantTwoSidedPullMarking_apply, giantTwoSidedPullAuxiliary_apply]
  exact congrArg₂ (·*·)
    (e.prod_comp (fun j => ∏ i ∈ Finset.univ \ C j, (a j (Fin.castAdd ell i)).val))
    (e.prod_comp (fun j => ∏ i : ↥(C j), (aux j i).val))

theorem giantTwoSidedPull_increment (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (κ : Fin n → ℤ) :
    giantTwoSidedLabelIncrement (fun i => C i ∘ e)
      (fun i => giantTwoSidedPullMarking e P (k+ell) (labels i))
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i)) κ =
      giantTwoSidedLabelIncrement C labels π aux κ := by
  funext i
  simp only [giantTwoSidedLabelIncrement, giantTwoSidedPull_permuteLabels, giantTwoSidedPull_dilation]

theorem giantTwoSidedPull_rootScalar (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedRootScalar (fun i => C i ∘ e) (fun i => giantTwoSidedPullMarking e P (k+ell) (labels i))
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i)) (fun i => giantTwoSidedPullSlots e (k+ell) (τ i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i)) ζ
      (fun i => giantTwoSidedPullCoefficient e P (K i)) =
      giantTwoSidedRootScalar C labels π τ aux ζ K := by
  have hm : markedPhysicalMass (fun a => bandReciprocalMass ((P ∘ e) a)) (k+ell) =
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) :=
    e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹^(k+ell))
  have ha (i : Fin n) : giantTwoSidedPatternAuxiliaryMass (giantTwoSidedPullAuxiliary e P (C i) (aux i)) =
      giantTwoSidedPatternAuxiliaryMass (aux i) := by
    simp only [giantTwoSidedPatternAuxiliaryMass, Function.comp_apply, giantTwoSidedPullAuxiliary_apply]
    exact e.prod_comp (fun j => ∏ l : ↥(C i j), markedHarmonicAtom (P j) (aux i j l))
  have hf (i : Fin n) : giantTwoSidedPatternFreshMass (P ∘ e) (C i ∘ e) ell =
      giantTwoSidedPatternFreshMass P (C i) ell :=
    e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹^(ell+(C i j).card))
  simp only [giantTwoSidedRootScalar, hm, ha, hf, giantTwoSidedPull_permuteLabels,
    giantTwoSidedPull_dilation, giantTwoSidedPullCoefficient, Equiv.symm_apply_apply]

end
end ArtinMatthews
