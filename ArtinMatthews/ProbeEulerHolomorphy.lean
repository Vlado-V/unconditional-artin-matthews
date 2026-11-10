module

public import ArtinMatthews.ProbeEulerNormalProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Joint complex differentiability of the good-prime product. The
multivariable step uses the actual Schwarz estimate for the derivatives
of the uniformly bounded local logarithms; it is not inferred merely
from separate differentiability. -/

namespace ArtinMatthews

noncomputable section
open NumberField IsDedekindDomain Set Filter Metric
open scoped NumberField Classical BigOperators Topology

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeLog_differentiableAt_coordinates
    (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    DifferentiableAt ℂ (probePrimeLog K a b c P.val) p :=
  probePrimeLog_differentiableAt K a b c ha hb hc S hS P
    differentiableAt_id.fst differentiableAt_id.snd.fst differentiableAt_id.snd.snd hp

theorem probeEulerLog_differentiableOn (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1) :
    DifferentiableOn ℂ (probeEulerLog K S a b c) (interior probeEulerDomain) := by
  intro p hp
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  have hsub : ball p R ⊆ probeEulerDomain := hball.trans interior_subset
  have hr : 0 < R / 2 := by positivity
  have hqsub {q : ProbeCoordinates} (hq : q ∈ ball p (R / 2)) :
      ball q (R / 2) ⊆ probeEulerDomain := by
    intro y hy
    apply hsub
    have hdist := dist_triangle y q p
    have hy' := Metric.mem_ball.mp hy
    have hq' := Metric.mem_ball.mp hq
    apply Metric.mem_ball.mpr
    linarith
  have hqmem {q : ProbeCoordinates} (hq : q ∈ ball p (R / 2)) : q ∈ probeEulerDomain :=
    hqsub hq (mem_ball_self hr)
  have hd (P : ProbeGoodPrime K S) (q : ProbeCoordinates) (hq : q ∈ ball p (R / 2)) :
      HasFDerivAt (probePrimeLog K a b c P.val)
        (fderiv ℂ (probePrimeLog K a b c P.val) q) q :=
    (probePrimeLog_differentiableAt_coordinates K a b c ha hb hc S hS P (hqmem hq)).hasFDerivAt
  have hderiv (P : ProbeGoodPrime K S) (q : ProbeCoordinates) (hq : q ∈ ball p (R / 2)) :
      ‖fderiv ℂ (probePrimeLog K a b c P.val) q‖ ≤
        (2 * (240 * probePrimeWeight K P.val)) / (R / 2) := by
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (fun y hy => (probePrimeLog_differentiableAt_coordinates K a b c ha hb hc S hS P
        (hqsub hq hy)).differentiableWithinAt) ?_ hr
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      _ ≤ ‖probePrimeLog K a b c P.val y‖ + ‖probePrimeLog K a b c P.val q‖ := norm_sub_le _ _
      _ ≤ 240 * probePrimeWeight K P.val + 240 * probePrimeWeight K P.val :=
        add_le_add (probePrimeLog_norm_le K a b c ha hb hc S hS P (hqsub hq hy))
          (probePrimeLog_norm_le K a b c ha hb hc S hS P (hqmem hq))
      _ = _ := by ring
  have hu : Summable (fun P : ProbeGoodPrime K S =>
      (2 * (240 * probePrimeWeight K P.val)) / (R / 2)) :=
    ((probeGoodPrime_majorant_summable K S).mul_left 2).div_const (R / 2)
  exact (hasFDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball p (R / 2)).isPreconnected
    hd hderiv (mem_ball_self hr)
      (probePrimeLog_summable K S hS a b c ha hb hc (interior_subset hp))
      (mem_ball_self hr)).differentiableAt.differentiableWithinAt

theorem probeEulerProduct_differentiableOn (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1) :
    DifferentiableOn ℂ (probeEulerProduct K S a b c) (interior probeEulerDomain) :=
  (probeEulerLog_differentiableOn K S hS a b c ha hb hc).cexp.congr
    (fun _ hp => probeEulerProduct_eq_exp K S hS a b c ha hb hc (interior_subset hp))

def probeEulerOpenDomain : Set ProbeCoordinates :=
  {p | (99799 / 100000 < p.1.re ∧ 299 / 100000 < p.2.1.re ∧ 39999 / 100000 < p.2.2.re) ∨
    (99799 / 100000 < p.1.re ∧ 94999 / 100000 < p.2.1.re ∧ 15999 / 100000 < p.2.2.re)}

theorem isOpen_probeEulerOpenDomain : IsOpen probeEulerOpenDomain := by
  have hx : Continuous (fun p : ProbeCoordinates => p.1.re) :=
    Complex.continuous_re.comp continuous_fst
  have hw : Continuous (fun p : ProbeCoordinates => p.2.1.re) :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_snd)
  have hz : Continuous (fun p : ProbeCoordinates => p.2.2.re) :=
    Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
  exact ((isOpen_lt continuous_const hx).inter
    ((isOpen_lt continuous_const hw).inter (isOpen_lt continuous_const hz))).union
    ((isOpen_lt continuous_const hx).inter
      ((isOpen_lt continuous_const hw).inter (isOpen_lt continuous_const hz)))

theorem probeEulerOpenDomain_subset_interior :
    probeEulerOpenDomain ⊆ interior probeEulerDomain := by
  have hs : probeEulerOpenDomain ⊆ probeEulerDomain := by
    intro p hp
    rcases hp with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩
    · exact Or.inl ⟨hx.le, hw.le, hz.le⟩
    · exact Or.inr ⟨hx.le, hw.le, hz.le⟩
  intro p hp
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (isOpen_probeEulerOpenDomain.mem_nhds hp) hs)

theorem probeEuler_manuscriptRegion_mem_interior {p : ProbeCoordinates}
    (hp : (499 / 500 ≤ p.1.re ∧ 3 / 1000 ≤ p.2.1.re ∧ 2 / 5 ≤ p.2.2.re) ∨
      (499 / 500 ≤ p.1.re ∧ 19 / 20 ≤ p.2.1.re ∧ 4 / 25 ≤ p.2.2.re)) :
    p ∈ interior probeEulerDomain := by
  apply probeEulerOpenDomain_subset_interior
  rcases hp with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩
  · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith⟩

/-- The unit-phase specialization of the literal rational correction product.
Its identification with the original local Gauss factors is separate. -/
def probeEulerPrincipalProduct (S : Finset (ProbePrime K)) : ProbeCoordinates → ℂ :=
  probeEulerProduct K S (fun _ => 1) (fun _ => 1) (fun _ => 1)

theorem probeEulerPrincipalProduct_ne_zero (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    probeEulerPrincipalProduct K S p ≠ 0 :=
  probeEulerProduct_ne_zero K S hS _ _ _ (by simp) (by simp) (by simp) hp

theorem probeEulerPrincipalProduct_differentiableOn (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) :
    DifferentiableOn ℂ (probeEulerPrincipalProduct K S) (interior probeEulerDomain) :=
  probeEulerProduct_differentiableOn K S hS _ _ _ (by simp) (by simp) (by simp)

theorem exists_probeEulerPrincipalProduct_uniform_half (S₀ : Finset (ProbePrime K)) :
    ∃ S : Finset (ProbePrime K), S₀ ⊆ S ∧ probePrimeCutoff K ⊆ S ∧
      ∀ p ∈ probeEulerDomain, ‖probeEulerPrincipalProduct K S p - 1‖ ≤ 1 / 2 := by
  obtain ⟨S, hS₀, hS, hs⟩ := exists_probeEulerSmallTail_above K S₀
  refine ⟨S, hS₀, hS, fun p hp => ?_⟩
  exact (probeEulerProduct_norm_sub_one_le K S hS (by linarith)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (by simp) (by simp) (by simp) hp).trans
      (by linarith)

end
end ArtinMatthews
