module

public import ArtinMatthews.HeckeExtension.ComplementCharacter
public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.SIntegerPrincipalExterior
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

/-! The actual source isotropic complement supplies a character of the
constructed S-integer ideal group. No ideal/principal descent is assumed. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain FractionalIdeal
open AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceComplementCharacter (χ : chosenB K hζ S₀ →* ℂˣ) :
    SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀) →* ℂˣ :=
  complementCharacter (G := SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)) (H := ℂˣ)
    (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) (chosenB K hζ S₀)
    (chosenB_isCompl K hζ S₀) χ

@[simp] theorem sourceComplementCharacter_allowed
    (χ : chosenB K hζ S₀ →* ℂˣ) (b : chosenB K hζ S₀) :
    sourceComplementCharacter K hζ S₀ χ b.val = χ b :=
  @complementCharacter_right (SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀))
    inferInstance ℂˣ inferInstance
    (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) (chosenB K hζ S₀)
    (chosenB_isCompl K hζ S₀) χ b

theorem sourceComplementCharacter_unit
    (χ : chosenB K hζ S₀ →* ℂˣ)
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    sourceComplementCharacter K hζ S₀ χ
      (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) u.val) = 1 := by
  exact @complementCharacter_left (SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀))
    inferInstance ℂˣ inferInstance
    (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) (chosenB K hζ S₀)
    (chosenB_isCompl K hζ S₀) χ
    ⟨_, ⟨u, rfl⟩⟩

def sourceComplementFieldCharacter (χ : chosenB K hζ S₀ →* ℂˣ) : Kˣ →* ℂˣ :=
  (sourceComplementCharacter K hζ S₀ χ).comp
    (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀))

theorem sourceComplementFieldCharacter_principal_kernel
    (χ : chosenB K hζ S₀ →* ℂˣ) :
    (toPrincipalIdeal (sourceRing K S₀) K).ker ≤
      (sourceComplementFieldCharacter K hζ S₀ χ).ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  have hu := (principal_eq_one_iff_sUnit K S₀ a).mp (MonoidHom.mem_ker.mp ha)
  exact sourceComplementCharacter_unit K hζ S₀ χ ⟨a, hu⟩

def sourceComplementIdealCharacter (χ : chosenB K hζ S₀ →* ℂˣ) : idealGroup K S₀ →* ℂˣ :=
  (toPrincipalIdeal (sourceRing K S₀) K).liftOfSurjective
    (exists_fractional_field_generator (sourceHilbertSeed K S₀))
    ⟨sourceComplementFieldCharacter K hζ S₀ χ,
      sourceComplementFieldCharacter_principal_kernel K hζ S₀ χ⟩

@[simp] theorem sourceComplementIdealCharacter_principal
    (χ : chosenB K hζ S₀ →* ℂˣ) (a : Kˣ) :
    sourceComplementIdealCharacter K hζ S₀ χ (toPrincipalIdeal (sourceRing K S₀) K a) =
      sourceComplementFieldCharacter K hζ S₀ χ a := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

theorem sourceComplementIdealCharacter_allowed
    (χ : chosenB K hζ S₀ →* ℂˣ) (a : allowedSubgroup K hζ S₀) :
    sourceComplementIdealCharacter K hζ S₀ χ (toPrincipalIdeal (sourceRing K S₀) K a.val) =
      χ ⟨sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val, a.property⟩ := by
  exact (sourceComplementIdealCharacter_principal K hζ S₀ χ a.val).trans
    (sourceComplementCharacter_allowed K hζ S₀ χ ⟨_, a.property⟩)

theorem sourceComplementIdealCharacter_sq
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1)
    (I : idealGroup K S₀) : sourceComplementIdealCharacter K hζ S₀ χ I ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := exists_fractional_field_generator (sourceHilbertSeed K S₀) I
  have he : sourceComplementIdealCharacter K hζ S₀ χ I =
      sourceComplementFieldCharacter K hζ S₀ χ a :=
    (congrArg (sourceComplementIdealCharacter K hζ S₀ χ) ha).symm.trans
      (sourceComplementIdealCharacter_principal K hζ S₀ χ a)
  apply (congrArg (fun z : ℂˣ => z ^ 2) he).trans
  exact hχ (complementProjection
    (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) (chosenB K hζ S₀)
    (chosenB_isCompl K hζ S₀) (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a))

end
end ArtinMatthews
