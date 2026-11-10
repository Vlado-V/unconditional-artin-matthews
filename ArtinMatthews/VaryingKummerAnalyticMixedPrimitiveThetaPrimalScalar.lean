module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacter
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleClearing
public import ArtinMatthews.VaryingKummerAnalyticRayIdealFixedCoefficients
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

/-! The primal fixed-ideal coefficient has an exact generator normalization.
This value, rather than merely its modulus, is needed for root-number coherence. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
namespace EvenIdealRayCharacter
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem fixedIdeal_coefficient_eq_generator (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMt : M ≠ ⊤) (G : Ideal (𝓞 K)) (hG : G ≠ ⊥)
    (hGM : IsCoprime G M) (hprodG : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (a : I) (ha : (a : 𝓞 K) ≠ 0)
    (hprod : Ideal.span {(a : 𝓞 K)} = I*J) :
    (if IsCoprime J M then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
        ψ.residue (idealResidueCoordinate I M hI hM a) := by
  obtain ⟨κ,_,H⟩ := ψ.exists_fixedIdeal_coefficient_residue hM I hI
  have Hg := H G hG
    ⟨idealModuleGenerator I M hI hM,idealModuleGenerator_mem I M hI hM⟩
    (idealModuleGenerator_ne_zero I M hI hM hMt) hprodG
  rw [ite_eq_left hGM,idealResidueCoordinate_generator,map_one,mul_one] at Hg
  rw [H J hJ a ha hprod,← Hg]

/-- A genuine coprime generator quotient fixes the scalar simultaneously
for every coefficient in the ordinary ideal class. -/
theorem exists_fixedIdeal_coefficient_generator (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMt : M ≠ ⊤) :
    ∃ (G : Ideal (𝓞 K)) (hG : G ≠ ⊥), IsCoprime G M ∧
      Ideal.span {idealModuleGenerator I M hI hM} = I*G ∧
      ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (a : I) (_ha : (a : 𝓞 K) ≠ 0)
        (_hprod : Ideal.span {(a : 𝓞 K)} = I*J),
        (if IsCoprime J M then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
          (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
            ψ.residue (idealResidueCoordinate I M hI hM a) := by
  obtain ⟨G,hG,hGM,hprodG⟩ := exists_idealModule_generator_coprime_quotient I M hI hM hMt
  exact ⟨G,hG,hGM,hprodG,ψ.fixedIdeal_coefficient_eq_generator hM I hI hMt G hG hGM hprodG⟩

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
