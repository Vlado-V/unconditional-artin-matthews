module

public import ArtinMatthews.QuotientUnitChanges
public import ArtinMatthews.SIntegerCharacterTransport
public import ArtinMatthews.ProbeIdealPoissonCRTHelpers
public import ArtinMatthews.ProbeIdealPoissonResidues
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

/-! Independence of the finite congruence kernel from representatives,
and transport across equal ideals. -/
namespace ArtinMatthews.SourceCRTNormalization

open ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.SIntegerQuotient
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]

theorem quotientCongruenceKernel_representatives (I J : Ideal R) (A H : R) (hAJ : A ∈ J)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : R ⧸ I → ℂ) (Z : R ⧸ J → ℂ)
    (drep : R ⧸ I → R) (vrep : R ⧸ J → R)
    (hdrep : ∀ d, Ideal.Quotient.mk I (drep d) = d)
    (hvrep : ∀ v, Ideal.Quotient.mk J (vrep v) = v) :
    quotientCongruenceKernel I J A H ψ W Z =
      ∑' d : R ⧸ I, ∑' v : R ⧸ J,
        if H - A * drep d ∈ I then W d * Z v *
          ψ (Ideal.Quotient.mk _ ((H - A * drep d) * vrep v)) else 0 := by
  unfold quotientCongruenceKernel
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  have hd : Quotient.out d - drep d ∈ I := by
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out, hdrep]
  have hv : Quotient.out v - vrep v ∈ J := by
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out, hvrep]
  have hg := probeIdealPoisson_gate_congr I A H _ _ hd
  by_cases hh : H - A * Quotient.out d ∈ I
  · rw [ite_eq_left hh, ite_eq_left (hg.mp hh),
      probeIdealPoisson_phase_congr_le I J (I * J) le_rfl A H _ _ _ _ hAJ hd hv hh]
  · rw [ite_eq_right hh, ite_eq_right (fun h => hh (hg.mpr h))]

theorem quotientEquivOfEq_refl (I : Ideal R) :
    Ideal.quotEquivOfEq (rfl : I = I) = RingEquiv.refl (R ⧸ I) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem quotientCongruenceKernel_transport {I J I' J' : Ideal R} (hI : I = I') (hJ : J = J')
    (A H : R) (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : R ⧸ I → ℂ) (Z : R ⧸ J → ℂ) :
    quotientCongruenceKernel I J A H ψ W Z =
      quotientCongruenceKernel I' J' A H
        (pullAddChar (Ideal.quotEquivOfEq (congrArg₂ (fun X Y : Ideal R => X * Y) hI hJ).symm) ψ)
        (fun d => W ((Ideal.quotEquivOfEq hI).symm d))
        (fun v => Z ((Ideal.quotEquivOfEq hJ).symm v)) := by
  cases hI
  cases hJ
  simp only [quotientEquivOfEq_refl, RingEquiv.symm_refl, RingEquiv.refl_apply]
  rfl

end
end ArtinMatthews.SourceCRTNormalization
