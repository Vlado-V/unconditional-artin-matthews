module

public import ArtinMatthews.SourceFrequencyNormSummability
public import ArtinMatthews.SourcePoissonInitialRows
public import ArtinMatthews.SourceContinuedPoissonMagnitude
public import ArtinMatthews.SourceFrequencyOrbitSeparation
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

/-! The actual orbit representatives are partitioned by their true norm.
The principal representative is removed exactly once. Every retained
row is nonsixth, and finite dyads inherit the genuine norm majorant. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceNonprincipalFrequencyIndex :=
  {i : SourceFrequencyRepresentativeIndex F S₀ // i ≠ sourceFrequencyPrincipalIndex F S₀}

abbrev SourceNonprincipalFrequencyDyad (j : ℕ) :=
  {i : SourceNonprincipalFrequencyIndex F S₀ //
    2^j ≤ sourceFrequencyRepresentativeNorm F S₀ i.val ∧
      sourceFrequencyRepresentativeNorm F S₀ i.val < 2^(j+1)}

instance sourceNonprincipalFrequencyDyad_finite (j : ℕ) : Finite (SourceNonprincipalFrequencyDyad F S₀ j) := by
  let : Finite (SourceBoundedFrequencyRows F S₀ (2^(j+1))) := sourceBoundedFrequencyRows_finite F S₀ _
  let f : SourceNonprincipalFrequencyDyad F S₀ j → SourceBoundedFrequencyRows F S₀ (2^(j+1)) :=
    fun i => ⟨i.val.val,i.property.2.le⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext (Subtype.ext
    (congrArg (fun t : SourceBoundedFrequencyRows F S₀ (2^(j+1)) => t.val) h)))

instance sourceNonprincipalFrequencyDyad_fintype (j : ℕ) : Fintype (SourceNonprincipalFrequencyDyad F S₀ j) :=
  Fintype.ofFinite _

private theorem subtype_fiber_heq {A : Type} {P : ℕ → A → Prop} {j k : ℕ} (h : j = k)
    (i : {x : A // P j x}) (t : {x : A // P k x}) (he : i.val = t.val) : HEq i t := by
  subst k
  exact heq_of_eq (Subtype.ext he)

def sourceNonprincipalFrequencyDyadEquiv :
    SourceNonprincipalFrequencyIndex F S₀ ≃ Σ j : ℕ, SourceNonprincipalFrequencyDyad F S₀ j where
  toFun i :=
    let q := sourceFrequencyRepresentativeNorm F S₀ i.val
    ⟨Nat.log 2 q, ⟨i, Nat.pow_log_le_self 2 (sourceFrequencyRepresentativeNorm_pos F S₀ i.val).ne',
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) q⟩⟩
  invFun i := i.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨j,i⟩
    have hj := Nat.log_eq_of_pow_le_of_lt_pow i.property.1 i.property.2
    apply Sigma.ext hj
    exact subtype_fiber_heq (P := fun k (x : SourceNonprincipalFrequencyIndex F S₀) =>
      2^k ≤ sourceFrequencyRepresentativeNorm F S₀ x.val ∧
        sourceFrequencyRepresentativeNorm F S₀ x.val < 2^(k+1)) hj _ _ rfl

theorem sourceNonprincipalFrequency_tsum_dyads (f : SourceNonprincipalFrequencyIndex F S₀ → ℂ)
    (hf : Summable f) :
    (∑' i, f i) = ∑' j : ℕ, ∑ i : SourceNonprincipalFrequencyDyad F S₀ j, f i.val := by
  let e := (sourceNonprincipalFrequencyDyadEquiv F S₀).symm
  have hs : Summable (fun i : Σ j : ℕ, SourceNonprincipalFrequencyDyad F S₀ j => f i.2.val) :=
    e.summable_iff.mpr hf
  calc
    _ = ∑' i : Σ j : ℕ, SourceNonprincipalFrequencyDyad F S₀ j, f i.2.val := (e.tsum_eq f).symm
    _ = _ := by
      have h := Summable.tsum_sigma' (fun j : ℕ => (hasSum_fintype (fun i : SourceNonprincipalFrequencyDyad F S₀ j => f i.val)).summable) hs
      simpa only [tsum_fintype] using h

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceNonprincipalFrequency_not_sixth (i : SourceNonprincipalFrequencyIndex F S₀) :
    ¬ ∃ a : F, a^6 = ((sourceFrequencyRepresentative F hζ S₀ i.val).val : F) := by
  rintro ⟨a,ha⟩
  apply i.property
  apply sourceFrequencyRepresentative_ratio_sixth_implies_eq F hζ S₀ i.val (sourceFrequencyPrincipalIndex F S₀)
  refine ⟨a,?_⟩
  rw [sourceFrequencyRepresentative_principal]
  simpa only [Subalgebra.coe_one, div_one] using ha.symm

theorem sourceNonprincipalFrequencyDyad_distinct_sixth {j : ℕ} (i k : SourceNonprincipalFrequencyDyad F S₀ j)
    (h : ∃ a : F, a^6 = ((sourceFrequencyRepresentative F hζ S₀ i.val.val).val : F) /
      ((sourceFrequencyRepresentative F hζ S₀ k.val.val).val : F)) : i = k := by
  obtain ⟨a,ha⟩ := h
  exact Subtype.ext (Subtype.ext (sourceFrequencyRepresentative_ratio_sixth_implies_eq F hζ S₀
    i.val.val k.val.val ⟨a,ha.symm⟩))

theorem sourceNonprincipalFrequencyDyad_frequency_bounds {j : ℕ} (i : SourceNonprincipalFrequencyDyad F S₀ j) :
    (2 : ℝ)^j ≤ sourcePoissonFrequencyNorm F S₀ (sourceFrequencyRepresentative F hζ S₀ i.val.val) ∧
      sourcePoissonFrequencyNorm F S₀ (sourceFrequencyRepresentative F hζ S₀ i.val.val) < 2*(2 : ℝ)^j := by
  rw [sourcePoissonFrequencyNorm_eq_exterior F S₀ hζ, sourceFrequencyRepresentativeNorm_eq_element F S₀ hζ]
  constructor
  · exact_mod_cast i.property.1
  · have h : (sourceFrequencyRepresentativeNorm F S₀ i.val.val : ℝ) < (2 : ℝ)^(j+1) := by
      exact_mod_cast i.property.2
    simpa only [pow_succ, mul_comm] using h

end
end ArtinMatthews.SourceEulerAssembly
