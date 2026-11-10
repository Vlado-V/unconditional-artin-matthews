module

public import ArtinMatthews.SourceKPTameIntertwiningShell
public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceJacquetShellAmplitude
public import ArtinMatthews.SourceKPTameIntertwiningAbsolute
public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceLocalHaarGeneralDilation
public import ArtinMatthews.StandardLocalBall
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary parameter-dependent local spherical Jacquet kernel at a
tame exterior place. The additive phase has the literal local frequency
and the shell integral uses the actual normalized Haar measure. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical VaryingKummerAnalytic
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "ν₀" => sourceLocalValuation K P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "shell₀" => sourceJacquetValuationShell K P.val

theorem sourceKPTraceJacquetFinitePhase_star_eq_neg
    (p : HeightOneSpectrum (𝓞 K)) (x : p.adicCompletion K) :
    star (localFiniteCharacter K p x) = localFiniteCharacter K p (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (localFiniteCharacter_unitary K p x)).symm

def sourceKPTraceJacquetLocalOrdinaryIntegrand (s : ℂ) (m x : L) : ZMod 3 → ℂ :=
  ψ₀ (-(m*x)) • sourceKPTameIntertwiningIntegrand K hζ S₀ P s x

theorem sourceKPTraceJacquetLocalOrdinaryIntegrand_eq_spherical (s : ℂ) (m x : L) :
    sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x =
      star (ψ₀ (m*x)) •
        (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val
          (sourceFiniteKP2ProjectiveLift K hζ P.val sourceGL2Weyl *
            sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Upper x)) := by
  rw [sourceKPTraceJacquetLocalOrdinaryIntegrand, sourceKPTameParametricSpherical_open K hζ S₀ P,
    sourceKPTraceJacquetFinitePhase_star_eq_neg K]

theorem sourceKPTraceJacquetLocalOrdinaryIntegrand_integrable
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (m : L) :
    Integrable (sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m) μ₀ := by
  let c : L → ℂ := fun x => ψ₀ (-(m*x))
  let f : L → ZMod 3 → ℂ := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  have hc : Continuous c :=
    (localFiniteCharacter_continuous K P.val).comp (continuous_const.mul continuous_id).neg
  have hf : Integrable f μ₀ := sourceKPTameIntertwiningIntegrand_integrable K hζ S₀ P hP hs
  change Integrable (fun x => c x • f x) μ₀
  refine hf.mono (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_smul, show ‖c x‖ = 1 from localFiniteCharacter_unitary K P.val (-(m*x)), one_mul]

def sourceKPTraceJacquetLocalOrdinary (s : ℂ) (m : L) : ZMod 3 → ℂ :=
  ∫ x, sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x ∂μ₀

theorem sourceKPTraceJacquetLocalOrdinary_shell (hP : P.val ∉ traceBadPlaces K)
    (s : ℂ) (m : L) (l : ℕ) :
    (∫ x in shell₀ (l : ℤ), sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x ∂μ₀) =
      (Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ)) *
        sourceJacquetShellIntegral K P.val (sourceJacquetShellCharacter K P.val χ₀ l)
          (m * ((π₀^(-(l : ℤ)) : Lˣ) : L))) • sourceJacquetBasis ((2*(l : ℤ) : ℤ) : ZMod 3) := by
  let t := π₀^(-(l : ℤ))
  let f := sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m
  let z := Complex.exp (-(2*s+1)*(l : ℂ)*(Real.log Q₀ : ℂ))
  let χ := sourceJacquetShellCharacter K P.val χ₀ l
  let A := fun u : L => sourceJacquetWeight K P.val χ u * ψ₀ (-((m*(t : L))*u))
  let b := sourceJacquetBasis ((2*(l : ℤ) : ℤ) : ZMod 3)
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P.val
  have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  have hi := sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht
  rw [zero_add] at hi
  have he : Set.EqOn (fun u => f ((t : L)*u)) (fun u => (z*A u) • b) (shell₀ 0) := by
    intro u hu
    change ψ₀ (-(m*((t : L)*u))) •
      sourceKPTameIntertwiningIntegrand K hζ S₀ P s ((t : L)*u) = _
    rw [sourceKPTameIntertwiningIntegrand_on_shell_image K hζ S₀ P s l u hu, smul_smul]
    change (ψ₀ (-(m*((t : L)*u))) * (z*sourceJacquetWeight K P.val χ u)) • b = (z*A u) • b
    rw [← mul_assoc m (t : L) u]
    congr 1
    dsimp only [A]
    ring
  change (∫ x in shell₀ (l : ℤ), f x ∂μ₀) = _
  rw [← hi, sourceLocalAddHaar_setIntegral_dilation K P.val μ₀ t _ f,
    setIntegral_congr_fun (sourceJacquetValuationShell_isCompact K P.val 0).measurableSet he,
    integral_smul_const, integral_const_mul]
  have hA : (∫ u in shell₀ 0, A u ∂μ₀) =
      sourceJacquetShellIntegral K P.val χ (m*(t : L)) :=
    sourceJacquetShellIntegral_eq_unit_shell K P.val χ _
  rw [hA, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (‖(t : L)‖ : ℂ) • ((z * sourceJacquetShellIntegral K P.val χ (m*(t : L))) • b) = _
  rw [sourceJacquetDilation_norm K P.val _ t ht, smul_smul]
  have hscale : sourceJacquetScale Q₀ ((l : ℤ) : ℝ) =
      Complex.exp ((l : ℂ)*(Real.log Q₀ : ℂ)) := by
    rw [sourceJacquetScale, Real.rpow_def_of_pos (sourceJacquetPrimeNorm_pos K S₀ P),
      Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [hscale, ← mul_assoc]
  dsimp only [z]
  rw [← Complex.exp_add]
  congr 3
  ring

end
end ArtinMatthews
