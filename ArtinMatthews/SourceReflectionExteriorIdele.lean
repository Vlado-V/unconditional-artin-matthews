module

public import ArtinMatthews.SourceFiniteDilationIdeal
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SIntegerPrincipalExterior
public import ArtinMatthews.SourcePrimeExponentValuation
public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.SourceSLocalExponentPoisson
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual S-local diagonal, extended by one, removes precisely the
retained finite components from a principal idele. Its exterior ideal is
the original source prime-exponent ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain FractionalIdeal AllowedGenerators SourcePhysical
open SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The finite part of the literal source diagonal. -/
def sourceReflectionFiniteDiagonal : Fˣ →* SFiniteUnits F S :=
  (MonoidHom.snd _ _).comp (sWholeDiagonal F S)

def sourceReflectionFiniteIdele : SFiniteUnits F S →* IdeleGroup F where
  toFun := IdeleGroup.ideleOfFiniteLocalFamily S
  map_one' := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext P
      by_cases hP : P ∈ S
      · exact IdeleGroup.finiteIdeleOfFinset_apply_mem S 1 ⟨P,hP⟩
      · exact IdeleGroup.finiteIdeleOfFinset_apply_notMem S 1 P hP
  map_mul' u v := by
    apply Prod.ext
    · exact (one_mul _).symm
    · apply Subtype.ext
      funext P
      change IdeleGroup.finiteIdeleOfFinset S (u*v) P =
        IdeleGroup.finiteIdeleOfFinset S u P * IdeleGroup.finiteIdeleOfFinset S v P
      by_cases hP : P ∈ S
      · simp only [IdeleGroup.finiteIdeleOfFinset_apply_mem S _ ⟨P,hP⟩, Pi.mul_apply]
      · simp only [IdeleGroup.finiteIdeleOfFinset_apply_notMem S _ P hP, mul_one]

theorem sourceReflectionFiniteIdele_apply_mem (u : SFiniteUnits F S) (P : S) :
    (sourceReflectionFiniteIdele F S u).2 P.val = u P :=
  IdeleGroup.finiteIdeleOfFinset_apply_mem S u P

theorem sourceReflectionFiniteIdele_apply_notMem (u : SFiniteUnits F S)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ S) :
    (sourceReflectionFiniteIdele F S u).2 P = 1 :=
  IdeleGroup.finiteIdeleOfFinset_apply_notMem S u P hP

theorem sourceReflectionFiniteDiagonal_apply (a : Fˣ) (P : S) :
    sourceReflectionFiniteDiagonal F S a P = (IdeleGroup.principalIdele F a).2 P.val := by
  apply Units.ext
  rfl

def sourceReflectionExteriorIdele : Fˣ →* IdeleGroup F :=
  IdeleGroup.principalIdele F /
    (sourceReflectionFiniteIdele F S).comp (sourceReflectionFiniteDiagonal F S)

theorem sourceReflectionExteriorIdele_apply_mem (a : Fˣ)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    (sourceReflectionExteriorIdele F S a).2 P = 1 := by
  change (IdeleGroup.principalIdele F a).2 P /
    (sourceReflectionFiniteIdele F S (sourceReflectionFiniteDiagonal F S a)).2 P = 1
  rw [sourceReflectionFiniteIdele_apply_mem F S _ ⟨P,hP⟩,
    sourceReflectionFiniteDiagonal_apply, div_self']

theorem sourceReflectionExteriorIdele_apply_notMem (a : Fˣ)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ S) :
    (sourceReflectionExteriorIdele F S a).2 P = (IdeleGroup.principalIdele F a).2 P := by
  change (IdeleGroup.principalIdele F a).2 P /
    (sourceReflectionFiniteIdele F S (sourceReflectionFiniteDiagonal F S a)).2 P = _
  rw [sourceReflectionFiniteIdele_apply_notMem F S _ P hP, _root_.div_one]

theorem sourceReflectionExteriorIdele_ideal_eq_principal_of_localUnits (a : Fˣ)
    (ha : ∀ P : S, sourceReflectionFiniteDiagonal F S a P ∈
      (P.val.adicCompletionIntegers F).units) :
    IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a) =
      toPrincipalIdeal (𝓞 F) F a := by
  let f := sourceReflectionFiniteIdele F S (sourceReflectionFiniteDiagonal F S a)
  have hf : IdeleGroup.fractionalIdeal f = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.fractionalIdeal_ker]
    intro P
    change f.2 P ∈ (P.adicCompletionIntegers F).units
    by_cases hP : P ∈ S
    · rw [sourceReflectionFiniteIdele_apply_mem F S _ ⟨P,hP⟩]
      exact ha ⟨P,hP⟩
    · rw [sourceReflectionFiniteIdele_apply_notMem F S _ P hP]
      exact (P.adicCompletionIntegers F).units.one_mem
  change IdeleGroup.fractionalIdeal (IdeleGroup.principalIdele F a / f) = _
  rw [map_div, hf, _root_.div_one, IdeleGroup.fractionalIdeal_principalIdele]

theorem sourceReflectionExteriorIdele_primeExponentIdeal
    {ζ : F} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) :
    IdeleGroup.fractionalIdeal
        (sourceReflectionExteriorIdele F (sourceHilbertSet F S₀) (sourcePrimeExponentUnit F hζ S₀ e)) =
      integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
        (sourcePrimeExponentIdeal_ne_bot F S₀ e) := by
  let a := sourcePrimeExponentUnit F hζ S₀ e
  let T := sourceHilbertSet F S₀
  let f := sourceReflectionExteriorIdele F T a
  let I := sourcePrimeExponentIdeal F S₀ e
  have hI : I ≠ ⊥ := sourcePrimeExponentIdeal_ne_bot F S₀ e
  apply FractionalIdealGroup.ext_count
  intro P
  change FractionalIdeal.count F P
      ((FractionalIdealGroup.factorization (FiniteIdeleGroup.valuationVector f.2) :
        FractionalIdealGroup F) : FractionalIdeal (𝓞 F)⁰ F) =
    FractionalIdeal.count F P (I : FractionalIdeal (𝓞 F)⁰ F)
  rw [FractionalIdealGroup.count_factorization, FiniteIdeleGroup.valuationVector_apply]
  by_cases hP : P ∈ T
  · rw [sourceReflectionExteriorIdele_apply_mem F T a P hP, map_one]
    change 0 = FractionalIdeal.count F P (I : FractionalIdeal (𝓞 F)⁰ F)
    have hD : ¬ P.asIdeal ∣ I :=
      ((exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) I).mp
        (sourcePrimeExponentIdeal_exterior F S₀ e)).2 P hP
    have hc : (Associates.mk P.asIdeal).count (Associates.mk I).factors = 0 :=
      not_ne_iff.mp ((Associates.count_ne_zero_iff_dvd hI P.irreducible).not.mpr hD)
    rw [FractionalIdeal.count_coe F P hI, hc]
    rfl
  · rw [sourceReflectionExteriorIdele_apply_notMem F T a P hP, FiniteIdeleGroup.localOrder_apply]
    change -WithZero.log (Valued.v (((IdeleGroup.principalIdele F a).2 P :
      (P.adicCompletion F)ˣ) : P.adicCompletion F)) = _
    have ha : (((IdeleGroup.principalIdele F a).2 P :
      (P.adicCompletion F)ˣ) : P.adicCompletion F) = ((a:F) : P.adicCompletion F) := rfl
    rw [ha, P.valuedAdicCompletion_eq_valuation', sourcePrimeExponentUnit_val,
      sourcePrimeExponentGenerator_valuation F hζ S₀ e ⟨P,hP⟩,
      WithZero.log_exp, neg_neg, sourcePrimeExponentIdeal_count_exterior F S₀ e ⟨P,hP⟩]

end
end ArtinMatthews.VaryingKummerAnalytic
