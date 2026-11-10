module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedContinuation
public import OAI.NumberTheory.DirichletL.FiniteFourier
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The primitive residue-one case has the actual unit ideal as conductor.
Its full ideal character therefore supplies an honest unramified class
series; no values at omitted primes are used to detect principality. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem idealConductor_top_of_primitive_residue_one {M : Ideal (𝓞 K)}
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) (h1 : χ = 1) : M = ⊤ := by
  by_contra hM
  let : Nontrivial ((𝓞 K) ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM
  obtain ⟨u,_,hu⟩ := hχ ⊤ top_ne_bot
  exact hu (by rw [h1,MulChar.one_apply u.isUnit])

namespace EvenIdealRayCharacter
variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

def IsNonprincipal : Prop :=
  ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
    IsCoprime I M ∧ ψ.idealHom (integralIdealFractionalUnit I hI) ≠ 1

omit [NumberField K] in
private theorem coprime_of_conductor_top (hM : M = ⊤) (I : Ideal (𝓞 K)) : IsCoprime I M := by
  rw [hM,← Ideal.one_eq_top]
  exact isCoprime_one_right

omit [NumberField K] in
private theorem quotient_eq_one_of_conductor_top (hM : M = ⊤) (a : 𝓞 K) :
    Ideal.Quotient.mk M a = 1 := by
  rw [← map_one (Ideal.Quotient.mk M)]
  apply Ideal.Quotient.eq.mpr
  rw [hM]
  trivial

def conductorOneRay (hM : M = ⊤) : EvenRayCharacter K 1 where
  idealHom := ψ.idealHom
  finiteOrder := ψ.finiteOrder
  residue := 1
  principalLaw := by
    intro a ha hac
    have H := ψ.principalLaw a ha (coprime_of_conductor_top hM _)
    rw [quotient_eq_one_of_conductor_top hM a,map_one] at H
    rw [H,MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hac)]

@[simp] theorem conductorOneRay_residue (hM : M = ⊤) : (ψ.conductorOneRay hM).residue = 1 := rfl

theorem conductorOneRay_coefficient (hM : M = ⊤) (J : integralFractionalIdeals K) :
    (ψ.conductorOneRay hM).coefficient J = ψ.coefficient J := by
  simp only [EvenRayCharacter.coefficient, EvenRayCharacter.coprime_modulus_one,
    coefficient,coprime_of_conductor_top hM,ite_true,conductorOneRay]

theorem conductorOneRay_dirichlet (hM : M = ⊤) (s : ℂ) :
    (ψ.conductorOneRay hM).dirichlet s = ψ.dirichlet s := by
  apply tsum_congr
  intro J
  rw [ψ.conductorOneRay_coefficient]

theorem conductorOneRay_isNonprincipal (hM : M = ⊤) (hψ : ψ.IsNonprincipal) :
    (ψ.conductorOneRay hM).IsNonprincipal := by
  obtain ⟨I,hI,_,hval⟩ := hψ
  exact ⟨I,hI,EvenRayCharacter.coprime_modulus_one I,hval⟩

def conductorOneContinued (hM : M = ⊤) : ℂ → ℂ :=
  (ψ.conductorOneRay hM).unramifiedContinued rfl

theorem conductorOneContinued_entire (hM : M = ⊤) :
    Differentiable ℂ (ψ.conductorOneContinued hM) :=
  (ψ.conductorOneRay hM).unramifiedContinued_entire rfl

theorem conductorOneContinued_eq_dirichlet (hM : M = ⊤) (hψ : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) : ψ.conductorOneContinued hM s = ψ.dirichlet s := by
  rw [conductorOneContinued,(ψ.conductorOneRay hM).unramifiedContinued_eq_dirichlet rfl
    (ψ.conductorOneRay_isNonprincipal hM hψ) hs,ψ.conductorOneRay_dirichlet]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
