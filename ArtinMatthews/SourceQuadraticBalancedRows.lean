module

public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SLocalRingBalancedCompact
public import ArtinMatthews.SourceElementExponents
public import ArtinMatthews.SourceBalancedGenerators
public import ArtinMatthews.SourceExponentFiniteFNorm
public import ArtinMatthews.SourceFrequencyNormOneAction
public import ArtinMatthews.SourcePoissonProbeRowBox
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceSixthUnitResidue
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical FractionalIdeal
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "V" => SLocalAdditiveCompletionSpace F S

private def sourceQuadraticBalancedPoint (u : (SLocalRing F S)ˣ) : V :=
  sourceSLocalUnitAdditivePoint F S (sLocalRingUnitsTopologicalEquiv F S u)

private def sourceQuadraticBalancedMap : ℝ × (SLocalRing F S)ˣ → V :=
  (fun p : ℝ × V => sourceProbeLogDilate F hζ S p.1 p.2) ∘
    (fun p : ℝ × (SLocalRing F S)ˣ => (p.1, sourceQuadraticBalancedPoint F S₀ p.2))

def sourceQuadraticBalancedBox : Set V :=
  sourceQuadraticBalancedMap F S₀ hζ '' (Set.Icc 0 (Real.log 2) ×ˢ sourceBalancedCompactSet F S)

theorem sourceQuadraticBalancedBox_isCompact :
    IsCompact (sourceQuadraticBalancedBox F S₀ hζ) := by
  have hPoint : Continuous (sourceQuadraticBalancedPoint F S₀) :=
    (sourceSLocalUnitAdditivePoint_continuous F S).comp (sLocalRingUnitsTopologicalEquiv F S).continuous
  have hPair : Continuous (fun p : ℝ × (SLocalRing F S)ˣ =>
      (p.1, sourceQuadraticBalancedPoint F S₀ p.2)) :=
    continuous_fst.prodMk (hPoint.comp continuous_snd)
  have hDilate : Continuous (fun p : ℝ × V => sourceProbeLogDilate F hζ S p.1 p.2) :=
    sourceProbeLogDilate_continuous F hζ S
  have hFun : Continuous (sourceQuadraticBalancedMap F S₀ hζ) := hDilate.comp hPair
  have hDom : IsCompact (Set.Icc (0 : ℝ) (Real.log 2) ×ˢ sourceBalancedCompactSet F S) :=
    isCompact_Icc.prod (sourceBalancedCompactSet_isCompact F S)
  unfold sourceQuadraticBalancedBox
  exact hDom.image hFun

omit [IsTotallyComplex F] in
private theorem sourceQuadraticBalancedGenerator_ratio (e : E) (b : OS) (hb : b ≠ 0)
    (hbI : (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {b})
    (hbA : Units.mk0 (b : F) (Subtype.coe_injective.ne hb) ∈ allowedSubgroup F hζ S₀) :
    ∃ v : OSˣ, b = a e * (v : OS) ^ 6 := by
  let u := Units.mk0 (b : F) (Subtype.coe_injective.ne hb)
  let w := sourcePrimeExponentUnit F hζ S₀ e
  have hI : toPrincipalIdeal OS F u = toPrincipalIdeal OS F w := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, sourcePrimeExponentUnit_val]
    change spanSingleton OS⁰ (b : F) = spanSingleton OS⁰ (a e : F)
    have he := congrArg (fun I : Ideal OS => (I : FractionalIdeal OS⁰ F))
      (hbI.symm.trans (sourcePrimeExponentGenerator_ideal F hζ S₀ e))
    rwa [coeIdeal_span_singleton, coeIdeal_span_singleton] at he
  obtain ⟨t, ht⟩ := allowed_ratio_sixth F hζ S₀ u w hbA (sourcePrimeExponentUnit_allowed F hζ S₀ e) hI
  let v := sourceExteriorUnitToSourceUnits F S₀ (sourceActualSUnitToExteriorUnit F S t)
  refine ⟨v, Subtype.ext ?_⟩
  have hu : u = (t : Fˣ) ^ 6 * w := by
    calc
      u = (u / w) * w := (div_mul_cancel u w).symm
      _ = _ := congrArg (fun z : Fˣ => z * w) ht
  have he := congrArg Units.val hu
  change (b : F) = (a e : F) * ((v : OS) : F) ^ 6
  have hv : (((v : OSˣ) : OS) : F) = ((t : Fˣ) : F) := rfl
  rw [hv, mul_comm]
  simpa only [u, w, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
    sourcePrimeExponentUnit_val] using he

omit [IsTotallyComplex F] in
/-- An actual balanced allowed row fits the common scaled box on every
positive norm dyad, and differs from the fixed generator by a sixth unit. -/
theorem exists_sourceQuadraticBalancedRow (e : E) {M : ℝ} (hM : 0 < M)
    (hlo : M ≤ (q e : ℝ)) (hhi : (q e : ℝ) ≤ 2 * M) :
    ∃ b : OS, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {b} ∧
      (∃ v : OSˣ, b = a e * (v : OS) ^ 6) ∧
      b ∈ sourceScaledLatticeRows F S₀ hζ (sourceQuadraticBalancedBox F S₀ hζ) M := by
  let I := sourcePrimeExponentRingIdealEquiv F S₀ e
  obtain ⟨b, hb, hI, hA, hB⟩ := source_balanced_integral_generator F hζ S₀ I
  refine ⟨b, hI, sourceQuadraticBalancedGenerator_ratio F S₀ hζ e b hb hI hA, ?_⟩
  have hCard : Nat.card (OS ⧸ I.val) = q e := by
    rw [show I.val = Ideal.span {a e} from sourcePrimeExponentGenerator_ideal F hζ S₀ e]
    exact sourcePrimeExponentGenerator_quotient_card F hζ S₀ e
  rw [hCard] at hB
  let u := Units.map (sLocalRingDiagonal F S).toMonoidHom
    (Units.mk0 (b : F) (Subtype.coe_injective.ne hb)) /
      sourceRingScaling F hζ S (q e : ℝ)
  let t := Real.log ((q e : ℝ) / M)
  let y := sourceProbeLogDilate F hζ S t (sourceQuadraticBalancedPoint F S₀ u)
  have hq : 0 < (q e : ℝ) := hM.trans_le hlo
  have hr : 0 < (q e : ℝ) / M := div_pos hq hM
  have hlog : t ∈ Set.Icc 0 (Real.log 2) :=
    ⟨Real.log_nonneg ((one_le_div hM).mpr hlo), Real.log_le_log hr ((div_le_iff₀ hM).mpr hhi)⟩
  have hy : y ∈ sourceQuadraticBalancedBox F S₀ hζ := ⟨(t, u), ⟨hlog, hB⟩, rfl⟩
  refine ⟨y, hy, ?_⟩
  change sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S M) * y =
    sLocalRingDiagonal F S (b : F)
  unfold y sourceProbeLogDilate
  rw [show Real.exp t = (q e : ℝ) / M from Real.exp_log hr]
  have hs := sLocalPositiveScaling_mul F hζ S hM hr
  rw [show M * ((q e : ℝ) / M) = q e by field_simp] at hs
  calc
    _ = sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S (q e : ℝ)) *
        sourceQuadraticBalancedPoint F S₀ u := by
      rw [hs, sourceSLocalUnitAdditivePoint_mul]
      ac_rfl
    _ = _ := by
      let l := sLocalPositiveScaling F hζ S (q e : ℝ)
      let d := sWholeDiagonal F S (Units.mk0 (b : F) (Subtype.coe_injective.ne hb))
      have hu : sLocalRingUnitsTopologicalEquiv F S u = d / l := by
        dsimp only [u, sourceRingScaling, d, l]
        rw [map_div, (sLocalRingUnitsTopologicalEquiv F S).apply_symm_apply,
          sLocalRingUnitsTopologicalEquiv_diagonal]
      unfold sourceQuadraticBalancedPoint
      rw [hu, ← sourceSLocalUnitAdditivePoint_mul]
      change sourceSLocalUnitAdditivePoint F S (l * (d / l)) = _
      rw [show l * (d / l) = d by rw [mul_comm, div_mul_cancel]]
      rfl

end
end ArtinMatthews.SourceEulerAssembly
