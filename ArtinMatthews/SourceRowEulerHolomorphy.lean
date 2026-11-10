module

public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.SourceGlobalCorrectionAnalytic
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nonprincipal source row is holomorphic on the proved
correction domain away from the remaining zeta pole and the literal
reciprocal denominator zeros. There is no additional w pole. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil Set
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sourceRayReciprocalDomain_of_one_lt_re {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥) (s : ℂ) (hs : 1 < s.re) :
    s ∈ sourceRayReciprocalDomain F ψ hM := by
  by_cases hψ : ψ.IsNonprincipal
  · rw [sourceRayReciprocalDomain, ite_eq_left hψ]
    change sourceRayNonprincipalContinued F ψ hM s ≠ 0
    rw [sourceRayNonprincipalContinued_eq_dirichlet F ψ hM hψ s hs]
    exact ψ.dirichlet_ne_zero hs
  · have h : s ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hs
      exact lt_irrefl _ hs
    rw [sourceRayReciprocalDomain, ite_eq_right hψ]
    change principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s ≠ 0
    rw [principalExteriorZetaRegularized_eq _ h,
      ← sourceRayPrincipal_dirichlet_eq_exteriorZeta F ψ hM hψ s hs]
    exact mul_ne_zero (sub_ne_zero.mpr h) (ψ.dirichlet_ne_zero hs)

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

local notation "S" => sourceHilbertSet F S₀
local notation "ω" => sourceRowKummerTwist F hζ S₀ u hu η hM
local notation "hMN" => mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S (sourceRowFieldUnit F S₀ u hu))

def sourceRowEulerOpenDomain : Set ProbeCoordinates :=
  (probeEulerOpenDomain ∩ {q : ProbeCoordinates | 6 * q.2.2 ≠ 1}) ∩
    {q : ProbeCoordinates | q.1 ∈ sourceRayReciprocalDomain F ω hMN}

theorem sourceRowEulerOpenDomain_isOpen :
    IsOpen (sourceRowEulerOpenDomain F hζ S₀ u hu η hM) := by
  have hz : IsOpen {q : ProbeCoordinates | 6 * q.2.2 ≠ (1 : ℂ)} :=
    (isOpen_ne : IsOpen {s : ℂ | s ≠ 1}).preimage (continuous_snd.snd.const_mul 6)
  exact (isOpen_probeEulerOpenDomain.inter hz).inter
    ((sourceRayReciprocalDomain_isOpen F ω hMN).preimage continuous_fst)

theorem sourceRowEulerOpenDomain_initial (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    (ξ, w, z) ∈ sourceRowEulerOpenDomain F hζ S₀ u hu η hM := by
  have h1 : 1 < (6 * z).re := by
    have he : ((6 : ℂ) * z).re = 6 * z.re := by norm_num [Complex.mul_re]
    rw [he]
    linarith
  have hz0 : 6 * z ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at h1
    exact lt_irrefl _ h1
  exact ⟨⟨Or.inr ⟨by dsimp; linarith, by dsimp; linarith, by dsimp; linarith⟩, hz0⟩,
    sourceRayReciprocalDomain_of_one_lt_re F ω hMN ξ (by linarith)⟩

theorem sourceRowEulerContinuation_differentiableOn
    (hcut : principalAngularCutoff F M ⊆ S)
    (hu₆ : ¬ ∃ a : F, a ^ 6 = (u : F)) :
    DifferentiableOn ℂ (sourceRowEulerContinuation F hζ S₀ u hu η hM)
      (sourceRowEulerOpenDomain F hζ S₀ u hu η hM) := by
  intro q hq
  rcases hq with ⟨⟨hE, hz⟩, hR⟩
  have hz' : 6 * q.2.2 ≠ (1 : ℂ) := hz
  have hZ : DifferentiableAt ℂ (principalExteriorZeta S) (6 * q.2.2) :=
    (mixedDedekindZeta_analyticAt F hz').differentiableAt.mul
      (principalZetaEulerFactor_entire S).differentiableAt
  have hN : DifferentiableAt ℂ (sourceRowNumeratorContinued F hζ S₀ u hu) q.2.1 :=
    (sourceRowNumeratorContinued_entire F hζ S₀ u hu hu₆).differentiableAt
  have hD : DifferentiableAt ℂ (sourceRowTwistReciprocal F hζ S₀ u hu η hM) q.1 :=
    ((sourceRayReciprocalContinued_differentiableOn F ω hMN) q.1 hR).differentiableAt
      ((sourceRayReciprocalDomain_isOpen F ω hMN).mem_nhds hR)
  have hC : DifferentiableAt ℂ (sourceGlobalCorrection F hζ S₀ η u hu) q :=
    ((sourceGlobalCorrection_differentiableOn F hζ S₀ η hM hcut u hu) q hE).differentiableAt
      (isOpen_probeEulerOpenDomain.mem_nhds hE)
  have hScale : DifferentiableAt ℂ (fun p : ProbeCoordinates => (6 : ℂ) * p.2.2) q :=
    differentiableAt_id.snd.snd.const_mul (6 : ℂ)
  exact ((((hZ.comp q hScale).mul
    (hN.comp q differentiableAt_id.snd.fst)).mul (hD.comp q differentiableAt_id.fst)).mul hC).differentiableWithinAt

theorem sourceRowEulerContinuation_analyticOnNhd_path
    (hcut : principalAngularCutoff F M ⊆ S) (hu₆ : ¬ ∃ a : F, a ^ 6 = (u : F))
    {U : Set ℂ} (hU : IsOpen U) (p : ℂ → ProbeCoordinates) (hp : DifferentiableOn ℂ p U)
    (hmem : MapsTo p U (sourceRowEulerOpenDomain F hζ S₀ u hu η hM)) :
    AnalyticOnNhd ℂ (sourceRowEulerContinuation F hζ S₀ u hu η hM ∘ p) U :=
  ((sourceRowEulerContinuation_differentiableOn F hζ S₀ u hu η hM hcut hu₆).comp hp hmem).analyticOnNhd hU

end
end ArtinMatthews.SourceEulerAssembly
