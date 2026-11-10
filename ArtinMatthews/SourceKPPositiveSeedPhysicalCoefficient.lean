module

public import ArtinMatthews.SourceKPPositivePhysicalFinite
public import ArtinMatthews.SourceKPRetainedExteriorWhittaker
public import ArtinMatthews.SourceKPRetainedThetaDepth
public import ArtinMatthews.SourceThetaFiniteMellin
public import ArtinMatthews.SourceKPRetainedPositiveAllFrequency
public import ArtinMatthews.SourceKPRetainedThetaRowMultiplier
public import ArtinMatthews.SourceReflectionPositiveRetainedTwist
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

/-! A single nonzero retained seed supplies the actual positive physical
tests, with the original fixed S and the same prescribed theta depth. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceReflection SourcePhysical QuadraticWeil
open VaryingKummerAnalytic StandardAdelic Matrix
open scoped NumberField Classical BigOperators MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "E" => SourcePrimeExponents K S₀
local notation "qbase" => sourceKPAdelicRootSupportTuple K hζ
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K

attribute [local instance] positiveTwistLabelFintype

structure SourceKPPositiveSeedData (hS : standardWeilBadPlaces K ⊆ S)
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {T : ℝ} (hT : 2 < T) where
  a : GL (Fin 2) 𝔸ᶠ[K]
  R : ↥S → ℕ
  M : ↥S → ℕ
  cutoff : ∀ P : S, SourceThetaFiniteCutoff K P.val
  coefficient_ne_zero :
    sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (qbase 1 a S).2 ≠ 0
  depth : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (cutoff P).region →
    ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val
      (-(sourceKPRetainedModulusDepth K S (sourceReflectionThetaModulus K S₀ hJ) P : ℤ)) ∧
      ∃ w, w^6 = t
  formula : ∀ (m : Kˣ) (z : ∀ P : S, (P.val.adicCompletion K)ˣ),
    let q₀ := (qbase 1 a S).2
    let C₀ := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀
    sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
      sourceKPRetainedSeedFourierAt K hζ S R M (one_le_two.trans hT.le) m q₀
        (D (sourceKPRetainedDiagonalUnit K S z)) =
    C₀ * (∏ P : S, (cutoff P).factor (sourceKPRetainedUnitAt K P.val (rUnit m) * z P)) *
      sourceKPRetainedExteriorWhittaker K hζ S₀ hS m

theorem sourceKPPositiveSeedData_nonempty (hS : standardWeilBadPlaces K ⊆ S)
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {T : ℝ} (hT : 2 < T) :
    Nonempty (SourceKPPositiveSeedData K hζ S₀ hS hJ hT) := by
  obtain ⟨a,R,M,W,hne,_,hd,h⟩ := sourceKPRetainedPositiveSeed_all_frequency_at_depth K hζ S₀ hS
    (sourceKPRetainedModulusDepth K S (sourceReflectionThetaModulus K S₀ hJ)) hT
  exact ⟨⟨a,R,M,W,hne,hd,h⟩⟩

def sourceKPPositiveSeedData_q₀ {hS : standardWeilBadPlaces K ⊆ S}
    {J : Ideal (𝓞 K)} {hJ : J ≠ ⊥} {T : ℝ} {hT : 2 < T}
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) : Gf :=
  (qbase 1 p.a S).2

def sourceKPPositivePhysicalTwistScalar (e : E)
    (mask : SourceReflectionPositiveTwistLabels K S₀ e → ℂ) (m : Kˣ) : ℂ :=
  ∑ h : SourceReflectionPositiveTwistLabels K S₀ e, mask h *
    sourceReflectionPositiveTwistWeight K hζ S₀ e h *
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K) * sourceReflectionPositiveTwistAdele K hζ S₀ e h)

theorem sourceKPPositivePhysicalFiniteCoefficient_factor (e : E) (R M : ↥S → ℕ)
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (mask : SourceReflectionPositiveTwistLabels K S₀ e → ℂ)
    (m : Kˣ) (x : Whole) :
    sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e R M hT q₀ mask m x =
      sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask m *
      (sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPRetainedSeedFourierAt K hζ S R M hT m q₀
          (D (sourceKPRetainedDiagonalUnit K S x.2))) := by
  let d := D (sourceKPRetainedDiagonalUnit K S x.2)
  let L := sourceKPCuspResidualFrequencyScale K hζ m (1/6)
  let W := sourceKPRetainedSeedFourierAt K hζ S R M hT m q₀
  unfold sourceKPPositivePhysicalFiniteCoefficient sourceKPPositivePhysicalTwistScalar
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  let y := sourceReflectionPositiveTwistAdele K hζ S₀ e h
  have hc : Commute (Nf y) d :=
    sourceReflectionPositiveTwistAdele_commute_retained K hζ S₀ e h x.2
  rw [sourceKPRetainedSeedFourierAt_unit_translate]
  change _ * (L * W (d * Nf y)) = _
  have hw : W (Nf y*d) = finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K)*y)*W d :=
    sourceReflectionRetainedSeedFourierAt_left_finite_upper K hζ S₀ R M m hT q₀ d y
  change _ = mask h * sourceReflectionPositiveTwistWeight K hζ S₀ e h *
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K)*y) * (L*W d)
  rw [hc.eq.symm,hw]
  ring

theorem sourceKPPositivePhysicalSeedCoefficient (hS : standardWeilBadPlaces K ⊆ S)
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {T : ℝ} (hT : 2 < T)
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) (e : E)
    (mask : SourceReflectionPositiveTwistLabels K S₀ e → ℂ) (m : Kˣ) (x : Whole) :
    let t := one_le_two.trans hT.le
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let C₀ := sourceKPCuspResidualFourierValue K hζ 1 t q₀
    sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e p.R p.M t q₀ mask m x =
      sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask m *
        (C₀ * (∏ P : S, (p.cutoff P).factor ((sWholeDiagonal K S m*x).2 P)) *
          sourceKPRetainedExteriorWhittaker K hζ S₀ hS m) := by
  dsimp only [sourceKPPositiveSeedData_q₀]
  rw [sourceKPPositivePhysicalFiniteCoefficient_factor]
  have h := p.formula m x.2
  simp_rw [sourceKPRetainedThetaShift_at K S m x] 
  exact congrArg (fun z : ℂ => sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask m * z) h

end
end ArtinMatthews
