module

public import ArtinMatthews.SourceFiniteUnitGauss
public import ArtinMatthews.SourceFiniteFourierNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The same quotient action reindexes the full finite source Fourier
sum and hence its literal double quotient coefficient F. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => PrincipalIntegerRing S₀

theorem sourcePeriodicFourier_mul_unit (s A : OS) (hs : s ≠ 0) (hA : A ≠ 0)
    (f : OS ⧸ Ideal.span {s} → ℂ) (g : OS ⧸ Ideal.span {A} → ℂ)
    (u : OSˣ) (hf : ∀ x, f (sourceQuotientMulUnit (Ideal.span {s}) u x) = f x)
    (hg : ∀ x, g (sourceQuotientMulUnit (Ideal.span {A}) u x) = g x) (h : OS) :
    sourcePeriodicFourier S₀ s A hs hA f g (h * (u : OS)) = sourcePeriodicFourier S₀ s A hs hA f g h := by
  let E := sourceQuotientMulUnit (Ideal.span {s * A}) u
  unfold sourcePeriodicFourier
  refine (tsum_congr (fun q => ?_)).trans (E.tsum_eq _)
  let x : OS := Quotient.out q
  let y : OS := Quotient.out (E q)
  have he : Ideal.Quotient.mk (Ideal.span {s * A}) (x * (u : OS)) = Ideal.Quotient.mk _ y := by
    rw [show Ideal.Quotient.mk (Ideal.span {s * A}) y = E q from Ideal.Quotient.mk_out _,
      ← sourceQuotientMulUnit_mk]
    exact congrArg E (Ideal.Quotient.mk_out q)
  have hes : Ideal.Quotient.mk (Ideal.span {s}) (x * (u : OS)) = Ideal.Quotient.mk _ y :=
    congrArg (quotientReduction s A) he
  have heA : Ideal.Quotient.mk (Ideal.span {A}) (x * (u : OS)) = Ideal.Quotient.mk _ y :=
    congrArg (oppositeReduction s A) he
  have hG : sourceResidueGauss S₀ s hs f (-y) = sourceResidueGauss S₀ s hs f (-x) := by
    calc
      _ = sourceResidueGauss S₀ s hs f (-(x * (u : OS))) :=
        sourceResidueGauss_eq_of_mk_eq S₀ s hs f (by rw [map_neg, map_neg, hes])
      _ = _ := by
        rw [← neg_mul]
        exact sourceResidueGauss_mul_unit S₀ s hs f u hf (-x)
  have hR : g (Ideal.Quotient.mk (Ideal.span {A}) y) = g (Ideal.Quotient.mk _ x) := by
    rw [← heA, ← sourceQuotientMulUnit_mk, hg]
  have hP : Ideal.Quotient.mk (Ideal.span {s * A}) ((h * (u : OS)) * x) =
      Ideal.Quotient.mk (Ideal.span {s * A}) (h * y) := by
    rw [show (h * (u : OS)) * x = h * (x * (u : OS)) by ring,
      map_mul (Ideal.Quotient.mk (Ideal.span {s * A})) h (x * (u : OS)),
      map_mul (Ideal.Quotient.mk (Ideal.span {s * A})) h y, he]
  change sourceResidueGauss S₀ s hs f (-x) * g (Ideal.Quotient.mk _ x) *
      sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)
        (Ideal.Quotient.mk _ ((h * (u : OS)) * x)) =
    sourceResidueGauss S₀ s hs f (-y) * g (Ideal.Quotient.mk _ y) *
      sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)
        (Ideal.Quotient.mk _ (h * y))
  rw [hG, hR, hP]

theorem sourceFiniteF_mul_unit_of_quotient_invariance (s A : OS) (hs : s ≠ 0) (hA : A ≠ 0)
    (hphase : (sIntegerQuotientPhase K (principalizingSet S₀) (s * A)
      (mul_ne_zero hs hA)).IsPrimitive)
    (f : OS ⧸ Ideal.span {s} → ℂ) (g : OS ⧸ Ideal.span {A} → ℂ)
    (u : OSˣ) (hf : ∀ x, f (sourceQuotientMulUnit (Ideal.span {s}) u x) = f x)
    (hg : ∀ x, g (sourceQuotientMulUnit (Ideal.span {A}) u x) = g x) (h : OS) :
    sourceFiniteF S₀ s A (h * (u : OS)) (fun x => f (Ideal.Quotient.mk _ x)) (fun x => g (Ideal.Quotient.mk _ x)) =
      sourceFiniteF S₀ s A h (fun x => f (Ideal.Quotient.mk _ x)) (fun x => g (Ideal.Quotient.mk _ x)) := by
  have he := sourcePeriodicFourier_mul_unit S₀ s A hs hA f g u hf hg h
  rw [sourcePeriodicFourier_eq S₀ s A hs hA hphase, sourcePeriodicFourier_eq S₀ s A hs hA hphase] at he
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (sourceQuotientNorm_pos S₀ s hs).ne') he

end
end ArtinMatthews.SIntegerFourier
