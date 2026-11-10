module

public import ArtinMatthews.SourceKPAdelicExceptionalCharacter
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourceKPIntegralResiduePhase
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

/-! The rational torus phase splits at the original retained places.
The exterior product is the exact inverse of the retained product. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceReflectionLocalTorusPhase (P : HeightOneSpectrum (𝓞 K))
    (t a : (P.adicCompletion K)ˣ) : ℂˣ :=
  sourceKPCentralComplex K hζ P (sourceFiniteKPHilbert K hζ P t a ^ 2)

def sourceReflectionRationalTorusPhase (t a : Kˣ) (P : HeightOneSpectrum (𝓞 K)) : ℂˣ :=
  let j := Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom
  sourceReflectionLocalTorusPhase K hζ P (j t) (j a)

theorem sourceReflectionRationalTorusPhase_eq (t a : Kˣ) (P : HeightOneSpectrum (𝓞 K)) :
    sourceReflectionRationalTorusPhase K hζ t a P =
      sourceKPAdelicCentralComplex K hζ (sourceRationalKPHilbert K hζ t a P ^ 2) := by
  let j := Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom
  let e := sourceKPRootsTransport K hζ P
  let z := sourceFiniteKPHilbert K hζ P (j t) (j a)
  have hz : e (sourceRationalKPHilbert K hζ t a P) = z := by
    have h := congrArg e (sourceKPRationalKPHilbert_transport K hζ P t a)
    change e (e.symm z) = _ at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  change sourceKPCentralComplex K hζ P (z ^ 2) = _
  rw [← hz, ← map_pow e, sourceKPAdelicCentralComplex_transport]

theorem sourceReflectionRationalTorusPhase_hasFiniteMulSupport (t a : Kˣ) :
    Function.HasFiniteMulSupport (sourceReflectionRationalTorusPhase K hζ t a) := by
  rw [funext (sourceReflectionRationalTorusPhase_eq K hζ t a)]
  exact ((sourceRationalKPHilbert_hasFiniteMulSupport K hζ t a).pow 2).fun_comp
    (map_one (sourceKPAdelicCentralComplex K hζ))

theorem sourceReflectionRationalTorusPhase_finprod (t a : Kˣ) :
    ∏ᶠ P, sourceReflectionRationalTorusPhase K hζ t a P = 1 := by
  calc
    _ = ∏ᶠ P, sourceKPAdelicCentralComplex K hζ (sourceRationalKPHilbert K hζ t a P ^ 2) :=
      finprod_congr (sourceReflectionRationalTorusPhase_eq K hζ t a)
    _ = sourceKPAdelicCentralComplex K hζ ((∏ᶠ P, sourceRationalKPHilbert K hζ t a P) ^ 2) := by
      let f (P : HeightOneSpectrum (𝓞 K)) := sourceRationalKPHilbert K hζ t a P ^ (2 : ℕ)
      have hf : Function.HasFiniteMulSupport f :=
        (sourceRationalKPHilbert_hasFiniteMulSupport K hζ t a).pow 2
      change (∏ᶠ P, sourceKPAdelicCentralComplex K hζ (f P)) = _
      rw [← (sourceKPAdelicCentralComplex K hζ).map_finprod hf]
      exact congrArg (sourceKPAdelicCentralComplex K hζ)
        (finprod_pow (sourceRationalKPHilbert_hasFiniteMulSupport K hζ t a) 2).symm
    _ = 1 := by rw [sourceRationalKPHilbert_finprod, one_pow, map_one]

theorem sourceReflectionRationalTorusPhase_exterior_finprod
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (t a : Kˣ) :
    (∏ᶠ P : SourceExteriorPrime K S₀, sourceReflectionRationalTorusPhase K hζ t a P.val) =
      (∏ P ∈ sourceHilbertSet K S₀, sourceReflectionRationalTorusPhase K hζ t a P)⁻¹ := by
  let f := sourceReflectionRationalTorusPhase K hζ t a
  let S := sourceHilbertSet K S₀
  have hf : Function.HasFiniteMulSupport f :=
    sourceReflectionRationalTorusPhase_hasFiniteMulSupport K hζ t a
  have hf' : (Set.univ ∩ Function.mulSupport f).Finite := by
    rw [Set.univ_inter]
    exact hf
  have h := finprod_mem_mul_sdiff' (f := f) (s := (S : Set (HeightOneSpectrum (𝓞 K))))
    (t := Set.univ) (Set.subset_univ _) hf'
  rw [finprod_mem_univ, ← Set.compl_eq_univ_sdiff, finprod_mem_coe_finset,
    ← finprod_set_coe_eq_finprod_mem] at h
  change (∏ P ∈ S, f P) * (∏ᶠ P : SourceExteriorPrime K S₀, f P.val) = ∏ᶠ P, f P at h
  rw [sourceReflectionRationalTorusPhase_finprod K hζ t a] at h
  change (∏ᶠ P : SourceExteriorPrime K S₀, f P.val) = (∏ P ∈ S, f P)⁻¹
  rw [← inv_mul_cancel_left (∏ P ∈ S, f P) (∏ᶠ P : SourceExteriorPrime K S₀, f P.val), h, mul_one]

end
end ArtinMatthews
