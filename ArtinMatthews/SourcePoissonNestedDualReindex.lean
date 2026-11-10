module

public import ArtinMatthews.SourcePoissonNestedDualGeometry
public import ArtinMatthews.SourcePoissonLiteralQuotientUnfold
public import ArtinMatthews.SourcePoissonActualSixthInvariance
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory SourcePhysical
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "H" => SourceNonzeroFrequency F S₀
local notation "U" => SourceFrequencyRepresentativeIndex F S₀
local notation "I" => SourcePoissonPhysicalOrbitIndex F S₀
local notation "L" => SourcePoissonNestedDualIndex F S₀
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "Γₐ" => SourceExteriorUnitSixthPowers S
local notation "eΓ" => sourceExteriorSixthNormOneEquiv F S
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "rep" => sourceFrequencyRepresentative F hζ S₀
local notation "amp" => sourcePoissonOrbitAmplitude F S₀ hζ hBad η
local notation "FourierW₀" => sourceSLocalCompletionFourier F S (sourceSLocalCompletionProbe F S)

/-- The signed dual coefficient and the full additive argument both transport exactly. -/
theorem sourcePoissonNestedDualTerm_orbit (X Y Z : ℝ) (t : SNormOne F S)
    (s : E) (c : C) (n : E) (u : U) (r : E) (γ : Γₐ) :
    sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s c n
        (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, γ)).val =
      amp X Y Z (rep u) (c, n, s, r) *
        FourierW₀ (sourceSLocalUnitAdditivePoint F S
          ((t : SWholeUnits F S) * (eΓ γ).val.val *
            sourcePoissonActualOrbitArgument F S₀ hζ X (u, (c, n, s, r)))) := by
  have hScalar :
      sourcePoissonNestedDualScalar F S₀ hζ hBad η X Y Z s c n
        (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, γ)).val =
      sourcePoissonNestedDualScalar F S₀ hζ hBad η X Y Z s c n
        ((rep u).val * a r ^ 6) := by
    unfold sourcePoissonNestedDualScalar
    dsimp only
    rw [sourceFrequencyOrbitEquiv_val,
      sourceExponentFiniteF_mul_orbitSixth F S₀ hζ hBad s (c.val + 3 • n)
        ((rep u).val * a r ^ 6) γ]
  rw [sourcePoissonNestedDualTerm, hScalar, sourcePoissonNestedDualScalar_representative,
    sourcePoissonNestedDualTransform_orbit]
  rfl

def sourcePoissonNestedDualJointTerm (X Y Z : ℝ) (t : SNormOne F S) (p : L) : ℂ :=
  sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t p.1 p.2.1.1 p.2.1.2 p.2.2.val

theorem sourcePoissonNestedDualJointTerm_reindex (X Y Z : ℝ) (t : SNormOne F S) (p : I × Γ) :
    sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t
        (sourcePoissonNestedDualIndexEquiv F S₀ hζ p) =
      amp X Y Z (rep p.1.1) p.1.2 *
        FourierW₀ (sourceSLocalUnitAdditivePoint F S
          ((t : SWholeUnits F S) * p.2.val.val *
            sourcePoissonActualOrbitArgument F S₀ hζ X p.1)) := by
  rcases p with ⟨⟨u, c, n, s, r⟩, b⟩
  let γ := (eΓ).symm b
  have hγ : eΓ γ = b := (eΓ).apply_symm_apply b
  rw [← hγ]
  exact (congrArg (sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t)
    (sourcePoissonNestedDualIndexEquiv_apply_orbit F S₀ hζ u c n s r γ)).trans
      (sourcePoissonNestedDualTerm_orbit F S₀ hζ hBad η X Y Z t s c n u r γ)

theorem sourcePoissonNestedDualDensity_eq_joint_of_summable
    (X Y Z : ℝ) (t : SNormOne F S)
    (h : Summable (fun p : L => ‖sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t p‖)) :
    sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t =
      ∑' p : L, sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t p := by
  let f := sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t
  have hf : Summable f := h.of_norm
  unfold sourcePoissonNestedDualDensity
  calc
    _ = ∑' s : E, ∑' p : (C × E) × H, f (s, p) :=
      tsum_congr fun s => (hf.prod_factor s).tsum_prod.symm
    _ = _ := hf.tsum_prod.symm

variable (v : InfinitePlace F)
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v

/-- Absolute convergence is transported from the positive physical sheet majorant. -/
theorem sourcePoissonNestedDualJoint_ae_summable {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∀ᵐ t ∂(ν).restrict D, Summable
      (fun p : L => ‖sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t p‖) := by
  filter_upwards [sourcePoissonLiteralFourierSeries_ae_summable F S₀ hζ hBad η v hX hY hZ]
    with t ht
  let e := sourcePoissonNestedDualIndexEquiv F S₀ hζ
  have h : Summable
      (fun p : I × Γ => ‖sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t (e p)‖) :=
    ht.congr fun p => congrArg norm
      (sourcePoissonNestedDualJointTerm_reindex F S₀ hζ hBad η X Y Z t p).symm
  exact e.summable_iff.mp h

theorem sourcePoissonNestedDualDensity_ae_eq_literal {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z =ᵐ[(ν).restrict D]
      sourcePoissonLiteralFourierSeries F S₀ hζ hBad η X Y Z := by
  filter_upwards [sourcePoissonNestedDualJoint_ae_summable F S₀ hζ hBad η v hX hY hZ]
    with t ht
  let e := sourcePoissonNestedDualIndexEquiv F S₀ hζ
  let f := sourcePoissonNestedDualJointTerm F S₀ hζ hBad η X Y Z t
  calc
    _ = ∑' p : L, f p :=
      sourcePoissonNestedDualDensity_eq_joint_of_summable F S₀ hζ hBad η X Y Z t ht
    _ = ∑' p : I × Γ, f (e p) := (e.tsum_eq f).symm
    _ = _ := tsum_congr (sourcePoissonNestedDualJointTerm_reindex F S₀ hζ hBad η X Y Z t)

/-- Integration of the actual nested dual density gives the literal orbit series. -/
theorem sourcePoissonNestedDualDensity_fundamentalIntegral {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z) ((ν).restrict D) ∧
      (∫ t in D, sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t ∂ν) =
        sourcePoissonActualOrbitSeries F S₀ hζ hBad η v X Y Z := by
  have h := sourcePoissonLiteralFundamentalIntegral F S₀ hζ hBad η v hX hY hZ
  have he := sourcePoissonNestedDualDensity_ae_eq_literal F S₀ hζ hBad η v hX hY hZ
  exact ⟨h.1.congr he.symm, (integral_congr_ae he).trans h.2⟩

end
end ArtinMatthews.SourceEulerAssembly
