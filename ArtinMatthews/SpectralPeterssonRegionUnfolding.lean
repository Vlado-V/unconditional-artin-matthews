module

public import ArtinMatthews.SpectralModularPartitionGamma0
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralModularPartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact L1 unfolding over the actual Gamma0 region. The covering
measure records both central representatives before cancellation in the
projective parabolic sum. -/

noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ENNReal

namespace ArtinMatthews

def gamma0PeterssonDomainPreimage (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    Set UpperHalfPlane :=
  (fun z : UpperHalfPlane => γ.val • z) ⁻¹' gamma0InteriorRegion N

private theorem gamma0Petersson_integer_smul_embedding (g : SL(2, ℤ)) :
    MeasurableEmbedding (fun z : UpperHalfPlane => g • z) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z)
  exact measurableEmbedding_const_smul _

theorem gamma0PeterssonDomainPreimage_measurableSet (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    MeasurableSet (gamma0PeterssonDomainPreimage N γ) :=
  (gamma0InteriorRegion_isOpen N).measurableSet.preimage
    (gamma0Petersson_integer_smul_embedding γ.val).measurable

private theorem gamma0Petersson_countable (N : ℕ) : Countable (CongruenceSubgroup.Gamma0 N) := by
  let _ : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let _ : Countable (SL(2, ℤ)) :=
    (show Function.Injective (fun g : SL(2, ℤ) => g.val) from Subtype.val_injective).countable
  exact (show Function.Injective (fun g : CongruenceSubgroup.Gamma0 N => g.val) from
    Subtype.val_injective).countable

theorem gamma0PeterssonDomain_indicator_tsum (N : ℕ) (F : UpperHalfPlane → ℝ≥0∞)
    {z : UpperHalfPlane} (hz : ∃ γ : CongruenceSubgroup.Gamma0 N,
      γ.val • z ∈ gamma0InteriorRegion N) :
    (∑' γ : CongruenceSubgroup.Gamma0 N, (gamma0PeterssonDomainPreimage N γ).indicator F z) =
      2*F z := by
  classical
  obtain ⟨γ,hγ⟩ := hz
  let η : CongruenceSubgroup.Gamma0 N := ⟨-γ.val, by
    simpa only [neg_one_mul] using
      (CongruenceSubgroup.Gamma0 N).mul_mem (gamma0_neg_one_mem N) γ.property⟩
  have hη : η.val = -γ.val := rfl
  have hne : γ ≠ η := by
    intro he
    have hg : γ.val = -γ.val := (congrArg Subtype.val he).trans hη
    have hh := congrArg (fun g : SL(2, ℤ) => g*γ.val⁻¹) hg
    have h1 : (1 : SL(2, ℤ)) = -1 := by simpa only [neg_mul,mul_inv_cancel] using hh
    have h0 := congrArg (fun g : SL(2, ℤ) => g 0 0) h1
    norm_num at h0
  have hηz : η.val • z ∈ gamma0InteriorRegion N := by
    rw [hη,ModularGroup.SL_neg_smul]
    exact hγ
  have hrest (δ : CongruenceSubgroup.Gamma0 N) (hδ : δ ∉ ({γ,η} : Finset _)) :
      (gamma0PeterssonDomainPreimage N δ).indicator F z = 0 := by
    apply indicator_of_notMem
    intro hd
    change δ.val • z ∈ gamma0InteriorRegion N at hd
    have hdz : (δ*γ⁻¹).val • (γ.val • z) ∈ gamma0InteriorRegion N := by
      change (δ.val*γ.val⁻¹) • (γ.val • z) ∈ gamma0InteriorRegion N
      simpa only [mul_smul,inv_smul_smul] using hd
    have hg := gamma0InteriorRegion_overlap_central N (δ*γ⁻¹) hγ hdz
    apply hδ
    rcases hg with hg | hg
    · have hh := congrArg (fun x : SL(2, ℤ) => x*γ.val) hg
      have he : δ.val = γ.val := by
        simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh
      exact Finset.mem_insert.mpr (Or.inl (Subtype.ext he))
    · have hh := congrArg (fun x : SL(2, ℤ) => x*γ.val) hg
      have he : δ.val = -γ.val := by
        simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel,mul_one,neg_one_mul] using hh
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext (he.trans hη.symm))))
  rw [tsum_eq_sum hrest,Finset.sum_pair hne]
  rw [indicator_of_mem (show z ∈ gamma0PeterssonDomainPreimage N γ from hγ),
    indicator_of_mem (show z ∈ gamma0PeterssonDomainPreimage N η from hηz),two_mul]

theorem gamma0PeterssonDomain_measureSum (N : ℕ) :
    Measure.sum (fun γ : CongruenceSubgroup.Gamma0 N => volume.restrict (gamma0PeterssonDomainPreimage N γ)) =
      (2 : ℝ≥0∞) • (volume : Measure UpperHalfPlane) := by
  let _ : Countable (CongruenceSubgroup.Gamma0 N) := gamma0Petersson_countable N
  ext t ht
  rw [Measure.sum_apply _ ht,Measure.smul_apply,smul_eq_mul]
  let F := t.indicator (fun _ : UpperHalfPlane => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator ht
  have he (γ : CongruenceSubgroup.Gamma0 N) :
      (volume.restrict (gamma0PeterssonDomainPreimage N γ)) t =
        ∫⁻ z, (gamma0PeterssonDomainPreimage N γ).indicator F z := by
    rw [lintegral_indicator (gamma0PeterssonDomainPreimage_measurableSet N γ)]
    dsimp only [F]
    rw [lintegral_indicator ht,lintegral_const]
    simp
  simp_rw [he]
  rw [← lintegral_tsum (fun γ => (hF.indicator (gamma0PeterssonDomainPreimage_measurableSet N γ)).aemeasurable)]
  calc
    _ = ∫⁻ z, (2 : ℝ≥0∞)*F z := by
      apply lintegral_congr_ae
      filter_upwards [gamma0InteriorRegion_covers_ae N] with z hz
      exact gamma0PeterssonDomain_indicator_tsum N F hz
    _ = _ := by
      rw [lintegral_const_mul _ hF]
      dsimp only [F]
      rw [lintegral_indicator ht,lintegral_const]
      simp

private theorem gamma0PeterssonDomain_integral_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) (F : UpperHalfPlane → E) :
    (∫ z in gamma0PeterssonDomainPreimage N γ, F z) =
      ∫ z in gamma0InteriorRegion N, F (γ.val⁻¹ • z) := by
  simpa only [gamma0PeterssonDomainPreimage,inv_smul_smul] using
    (h2_integer_measurePreserving γ.val).setIntegral_preimage_emb
      (gamma0Petersson_integer_smul_embedding γ.val)
      (fun z : UpperHalfPlane => F (γ.val⁻¹ • z)) (gamma0InteriorRegion N)

theorem gamma0PeterssonRegion_integral_unfold (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Integrable F) :
    (∫ z in gamma0InteriorRegion N, ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z)) =
      (2 : ℂ)*(∫ z, F z) := by
  let _ : Countable (CongruenceSubgroup.Gamma0 N) := gamma0Petersson_countable N
  let μ (γ : CongruenceSubgroup.Gamma0 N) := volume.restrict (gamma0PeterssonDomainPreimage N γ)
  let ρ := volume.restrict (gamma0InteriorRegion N)
  have hμ : Measure.sum μ = (2 : ℝ≥0∞) • (volume : Measure UpperHalfPlane) :=
    gamma0PeterssonDomain_measureSum N
  have hFμ : Integrable F (Measure.sum μ) := by
    rw [hμ]
    exact hF.smul_measure (by norm_num)
  have hI (γ : CongruenceSubgroup.Gamma0 N) :
      Integrable (fun z : UpperHalfPlane => F (γ.val⁻¹ • z)) ρ := by
    have h := ((h2_integer_measurePreserving γ.val).restrict_preimage_emb
      (gamma0Petersson_integer_smul_embedding γ.val) (gamma0InteriorRegion N)).integrable_comp_emb
      (gamma0Petersson_integer_smul_embedding γ.val) (g := fun z => F (γ.val⁻¹ • z))
    apply h.mp
    simpa only [Function.comp_def,inv_smul_smul,gamma0PeterssonDomainPreimage] using
      (hF.restrict (s := gamma0PeterssonDomainPreimage N γ))
  have hS : Summable (fun γ : CongruenceSubgroup.Gamma0 N => ∫ z, ‖F (γ.val⁻¹ • z)‖ ∂ρ) :=
    hFμ.summable_integral.congr (fun γ =>
      gamma0PeterssonDomain_integral_translate N γ (fun z => ‖F z‖))
  change (∫ z, ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z) ∂ρ) = _
  rw [← integral_tsum_of_summable_integral_norm hI hS]
  calc
    _ = ∑' γ : CongruenceSubgroup.Gamma0 N, ∫ z, F z ∂μ γ :=
      tsum_congr fun γ => (gamma0PeterssonDomain_integral_translate N γ F).symm
    _ = ∫ z, F z ∂Measure.sum μ := (integral_sum_measure hFμ).symm
    _ = _ := by rw [hμ,integral_smul_measure]; norm_num [Complex.real_smul]

end ArtinMatthews
