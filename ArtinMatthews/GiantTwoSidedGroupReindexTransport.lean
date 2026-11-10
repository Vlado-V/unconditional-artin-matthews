module

public import ArtinMatthews.GiantTwoSidedExpandedFourier
public import ArtinMatthews.GiantTwoSidedGroupReindexFourier
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

/-! The exact group reindexing with pointwise identified bands and
copied sets. Coordinate transports preserve the underlying primes. -/
namespace ArtinMatthews
noncomputable section

variable {A J : Type*} (e : A ≃ J) {P : J → Finset ℕ} {Q : A → Finset ℕ}

def giantTwoSidedPullMarkingOf (hP : ∀ j, Q j = P (e j)) {M : ℕ}
    (a : MarkedPhysicalMarking P M) : MarkedPhysicalMarking Q M :=
  fun j l => ⟨(a (e j) l).val, (hP j).symm ▸ (a (e j) l).property⟩

def giantTwoSidedPullAuxiliaryOf (hP : ∀ j, Q j = P (e j)) {k : ℕ}
    {C : J → Finset (Fin k)} {C' : A → Finset (Fin k)} (hC : ∀ j, C' j = C (e j))
    (z : GiantTwoSidedPatternAuxiliary P C) : GiantTwoSidedPatternAuxiliary Q C' :=
  fun j l =>
    let l' : ↥(C (e j)) := ⟨l.val, hC j ▸ l.property⟩
    ⟨(z (e j) l').val, (hP j).symm ▸ (z (e j) l').property⟩

theorem giantTwoSidedExpandedIndependentFourierMoment_reindex {I : Type*}
    [Fintype A] [Fintype J] [DecidableEq A] [DecidableEq J]
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes Q), NeZero p.val]
    (hP : ∀ j, Q j = P (e j)) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (C' : Fin n → I → A → Finset (Fin k))
    (hC : ∀ i p j, C' i p j = C i p (e j)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i p, GiantTwoSidedPatternCoefficient P (C i p) ell)
    (K' : ∀ i p, GiantTwoSidedPatternCoefficient Q (C' i p) ell)
    (hK : ∀ i p a b aux,
      K' i p (giantTwoSidedPullMarkingOf e hP a) (giantTwoSidedPullMarkingOf e hP b)
        (giantTwoSidedPullAuxiliaryOf e hP (hC i p) aux) = K i p a b aux)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedExpandedIndependentFourierMoment patterns C' κ q ζ K' θ =
      giantTwoSidedExpandedIndependentFourierMoment patterns C κ q ζ K θ := by
  have hPQ : Q = P ∘ e := funext hP
  subst Q
  have hCC : C' = fun i p => C i p ∘ e := funext (fun i => funext (fun p => funext (hC i p)))
  subst C'
  have hM (a : MarkedPhysicalMarking P (k+ell)) : giantTwoSidedPullMarkingOf e hP a =
      giantTwoSidedPullMarking e P (k+ell) a := by
    funext j l
    apply Subtype.ext
    simp only [giantTwoSidedPullMarkingOf, giantTwoSidedPullMarking_apply]
  have ha (i : Fin n) (p : I) (z : GiantTwoSidedPatternAuxiliary P (C i p)) :
      giantTwoSidedPullAuxiliaryOf e hP (hC i p) z = giantTwoSidedPullAuxiliary e P (C i p) z := by
    funext j l
    apply Subtype.ext
    simp only [giantTwoSidedPullAuxiliaryOf, giantTwoSidedPullAuxiliary_apply]
    cases l
    rfl
  have hK' : K' = fun i p => giantTwoSidedPullCoefficient e P (K i p) := by
    funext i p a b z
    obtain ⟨a,rfl⟩ := (giantTwoSidedPullMarking e P (k+ell)).surjective a
    obtain ⟨b,rfl⟩ := (giantTwoSidedPullMarking e P (k+ell)).surjective b
    obtain ⟨z,rfl⟩ := (giantTwoSidedPullAuxiliary e P (C i p)).surjective z
    simpa only [hM, ha, giantTwoSidedPullCoefficient, Equiv.symm_apply_apply] using hK i p a b z
  rw [hK']
  exact giantTwoSidedExpandedIndependentFourierMoment_pull e P hdis patterns C κ q ζ K θ

end
end ArtinMatthews
